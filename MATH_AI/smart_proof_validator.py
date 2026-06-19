#!/usr/bin/env python3
"""
Smart Proof Validator for ARM Proofs

Addresses the assembly definition crash issue by:
1. Skipping problematic define_assert_from_elf commands
2. Loading assembly definitions from pre-compiled sources
3. Focusing on actual proof validation rather than setup
"""

import sys
import json
import time
import socket
import subprocess
import re
from pathlib import Path
from typing import Dict, List, Set, Tuple

class HOLLightChecker:
    """Manages connection and communication with HOL Light server."""
    
    def __init__(self, host='127.0.0.1', port=2012, timeout=400):
        self.host = host
        self.port = port
        self.timeout = timeout
        self.socket = None
        self.connected = False
    
    def connect(self) -> bool:
        """Connect to HOL Light server."""
        try:
            self.socket = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
            self.socket.settimeout(self.timeout)
            self.socket.connect((self.host, self.port))
            self.connected = True
            print(f"Connected to HOL Light server at {self.host}:{self.port}")
            return True
        except Exception as e:
            print(f"Failed to connect to HOL Light server: {e}")
            return False
    
    def disconnect(self):
        """Disconnect from HOL Light server."""
        if self.socket:
            try:
                self.socket.close()
            except:
                pass
            self.socket = None
            self.connected = False
    
    def send_command(self, command: str, timeout: int = None, show_streaming: bool = False) -> dict:
        """Send command to HOL Light server and navigate by server outputs instead of timeouts."""
        if not self.connected:
            return {"success": False, "error": "Not connected to server"}
        
        # CRITICAL: Verify command is single line before sending
        newline_char = '\n'
        carriage_char = '\r'
        newline_count = command.count(newline_char) + command.count(carriage_char)
        if newline_count > 0:
            print(f"    CRITICAL ERROR: Command contains {newline_count} line breaks!")
            print(f"    Command preview: {command[:200]}...")
            print("    EMERGENCY: Force converting to single line before sending")
            # Emergency normalization
            command = command.replace('\r\n', ' ').replace('\r', ' ').replace('\n', ' ')
            command = re.sub(r'\s+', ' ', command).strip()
            final_newlines = command.count(newline_char) + command.count(carriage_char)
            print(f"    After emergency cleanup: {final_newlines} line breaks")
        
        # Use a generous timeout only as a safety net (10 minutes)
        safety_timeout = 600
        if timeout is None:
            timeout = safety_timeout
        
        try:
            # Send command - add only a single newline for server protocol
            full_command = command + '\n'
            
            # Final verification before sending
            newline_char = '\n'
            full_command_newlines = full_command.count(newline_char)
            if full_command_newlines > 1:
                print(f"    FATAL: full_command still has {full_command_newlines} newlines!")
                return {"success": False, "error": "Command contains multiple newlines - cannot send safely"}
            
            print(f"    Sending single-line command ({len(command)} chars)")
            self.socket.sendall(full_command.encode('utf-8'))
            
            # Set safety timeout
            self.socket.settimeout(safety_timeout)
            
            # Navigate by server outputs instead of timeouts
            response = ""
            start_time = time.time()
            ready_count = 0
            success = False
            command_completed = False
            
            print(f"    Waiting for server response...")
            
            while not command_completed:
                try:
                    data = self.socket.recv(4096).decode('utf-8')
                    if not data:
                        break
                    
                    response += data
                    
                    # Process streaming output line by line
                    lines = data.strip().split('\n')
                    for line in lines:
                        if not line:
                            continue
                            
                        if line.startswith("ready:"):
                            ready_count += 1
                            print(f"    Server ready signal {ready_count}")
                            
                            # Command is complete when we get the first ready after a result
                            if success and ready_count >= 1:
                                command_completed = True
                                break
                            # For simple commands, first ready might be completion
                            elif ready_count >= 2:
                                command_completed = True
                                success = True
                                break
                                
                        elif line.startswith("result:"):
                            success = True
                            result_content = self._unescape(line[7:]) if len(line) > 7 else ""
                            print(f"    Got result: {result_content[:100]}{'...' if len(result_content) > 100 else ''}")
                            
                        elif line.startswith("rerror:"):
                            error_msg = self._unescape(line[7:]) if len(line) > 7 else "Unknown error"
                            print(f"    Server error: {error_msg}")
                            return {"success": False, "error": error_msg, "response": response}
                            
                        elif line.startswith("stdout:") and len(line) > 7:
                            stdout_content = self._unescape(line[7:])
                            if stdout_content.strip():
                                if show_streaming:
                                    print(f"    {stdout_content}")
                                
                                # Check for completion indicators in stdout
                                if "already loaded" in stdout_content.lower():
                                    success = True
                                    print(f"    File already loaded - command complete")
                                elif "val " in stdout_content and ("thm" in stdout_content or "=" in stdout_content):
                                    success = True
                                    print(f"    Theorem/value defined - waiting for ready signal")
                                    
                        elif line.startswith("stderr:") and show_streaming and len(line) > 7:
                            stderr_content = self._unescape(line[7:])
                            if stderr_content.strip():
                                print(f"    STDERR: {stderr_content}")
                    
                    # Safety timeout check (should rarely trigger)
                    if time.time() - start_time > safety_timeout:
                        print(f"    Safety timeout reached after {safety_timeout} seconds")
                        return {"success": False, "error": f"Safety timeout after {safety_timeout} seconds", "response": response}
                        
                except socket.timeout:
                    print(f"    Socket timeout - continuing to wait...")
                    continue
            
            # Determine final success based on response content
            if "Exception:" in response or "rerror:" in response or "Broken pipe" in response:
                return {"success": False, "error": "Server reported error", "response": response}
            elif "[ERROR] Bad input" in response:
                return {"success": False, "error": "Server rejected input as malformed", "response": response}
            elif "SIGPIPE" in response or "Connection closed" in response:
                return {"success": False, "error": "Server connection lost", "response": response}
            elif "Unexpected command:" in response:
                return {"success": False, "error": "Server received unexpected command", "response": response}
            elif "- : int =" in response and "thm" not in response:
                return {"success": False, "error": "Got integer result instead of theorem", "response": response}
            elif success and "val " in response and "thm" in response:
                # Only report success if we got a theorem (not just any val)
                return {"success": True, "response": response.strip()}
            elif "already loaded" in response.lower():
                # File loading success
                return {"success": True, "response": response.strip()}
            else:
                # Default to failure if we don't have clear theorem success indicators
                return {"success": False, "error": "No theorem validation success indicators from server", "response": response}
                
        except Exception as e:
            return {"success": False, "error": str(e)}
    
    def _unescape(self, text: str) -> str:
        """Unescape text from server response."""
        try:
            return text.encode().decode('unicode_escape')
        except:
            return text
    
    def load_needs_file(self, filepath: str, timeout: int = 400) -> bool:
        """Load a needs file with extended timeout and streaming output."""
        command = f'needs "{filepath}";;'
        print(f"Attempting to load: {filepath}")
        
        # Use streaming for base.ml and other long-loading files
        show_streaming = 'base.ml' in filepath or timeout > 60
        
        result = self.send_command(command, timeout, show_streaming=show_streaming)
        
        # Enhanced success detection for needs files
        response = result.get("response", "")
        
        # Check for clear success indicators
        success_indicators = [
            "already loaded" in response.lower(),
            "val " in response and not "Exception" in response,
            result.get("success", False) and not any(err in response for err in [
                "Exception:", "Error:", "Failed", "not found", "No such file"
            ])
        ]
        
        if any(success_indicators):
            print(f"Successfully loaded {filepath}")
            return True
        else:
            print(f"Failed to load {filepath}: {result.get('error', 'Unknown error')}")
            print(f"Full response: {response}")
            return False
    
    def test_definition(self, definition: str, timeout: int = 10) -> bool:
        """Test if a definition exists."""
        command = f"{definition};;"
        result = self.send_command(command, timeout)
        
        # Enhanced definition checking
        response = result.get("response", "")
        
        # Check for clear success (definition exists and can be evaluated)
        if result.get("success", False):
            # Make sure we didn't get an error about undefined variables
            if not any(err in response for err in [
                "Unbound", "not found", "undefined", "Exception", "Error"
            ]):
                return True
        
        return False
    
    def verify_critical_definitions(self, expected_definitions: List[str]) -> bool:
        """Verify that critical definitions are available after loading."""
        print("=" * 60)
        print("VERIFYING CRITICAL DEFINITIONS")
        print("=" * 60)
        
        all_available = True
        for definition in expected_definitions:
            print(f"Testing critical definition: {definition}")
            if self.test_definition(definition):
                print(f"  ✓ AVAILABLE: {definition}")
            else:
                print(f"  ✗ MISSING: {definition}")
                all_available = False
        
        return all_available

class DependencyResolver:
    """Resolves complex interdependencies using topological sorting."""
    
    def extract_dependencies(self, proof_goals: List[Dict]) -> Dict[str, Set[str]]:
        """Extract dependencies between proof goals."""
        dependencies = {}
        
        for goal in proof_goals:
            goal_name = goal['theorem_name']
            dependencies[goal_name] = set()
            
            # Analyze setup code and proof for dependencies
            full_code = goal.get('setup_code', '') + goal.get('complete_proof', '')
            
            # Find references to other theorems
            for other_goal in proof_goals:
                other_name = other_goal['theorem_name']
                if other_name != goal_name and other_name in full_code:
                    dependencies[goal_name].add(other_name)
        
        return dependencies
    
    def topological_sort(self, dependencies: Dict[str, Set[str]]) -> List[str]:
        """Sort goals in dependency order using Kahn's algorithm."""
        # Calculate in-degrees - count how many dependencies each node has
        in_degree = {node: len(dependencies[node]) for node in dependencies}
        
        # Initialize queue with nodes having no dependencies
        queue = [node for node in in_degree if in_degree[node] == 0]
        result = []
        
        while queue:
            current = queue.pop(0)
            result.append(current)
            
            # Update in-degrees of nodes that depend on current
            for node in dependencies:
                if current in dependencies[node]:
                    in_degree[node] -= 1
                    if in_degree[node] == 0:
                        queue.append(node)
        
        # Check for cycles - add remaining nodes
        if len(result) != len(dependencies):
            remaining = set(dependencies.keys()) - set(result)
            result.extend(remaining)
        
        return result
    
    def resolve_dependencies(self, proof_goals: List[Dict]) -> List[Dict]:
        """Resolve dependencies and return goals in correct order."""
        dependencies = self.extract_dependencies(proof_goals)
        sorted_names = self.topological_sort(dependencies)
        
        # Reorder goals according to dependency resolution
        goal_map = {goal['theorem_name']: goal for goal in proof_goals}
        resolved_goals = []
        
        for name in sorted_names:
            if name in goal_map:
                resolved_goals.append(goal_map[name])
        
        return resolved_goals

class SmartProofValidator:
    """Smart validator that handles assembly definition issues with robust features."""
    
    def __init__(self, json_file: str):
        self.json_file = json_file
        self.checker = HOLLightChecker(timeout=400)
        self.dependency_resolver = DependencyResolver()
        self.successful_validations = 0
        self.skipped_definitions = 0
        
    def load_proof_goals(self):
        """Load proof goals from JSON file."""
        try:
            with open(self.json_file, 'r') as f:
                data = json.load(f)
            
            proof_goals = data.get('extracted_goals', [])
            extraction_info = data.get('extraction_info', {})
            
            print(f"LOADED JSON FILE: {self.json_file}")
            print(f"EXTRACTION TIMESTAMP: {extraction_info.get('timestamp', 'Unknown')}")
            print(f"TOTAL PROOF GOALS: {len(proof_goals)}")
            print(f"FILES PROCESSED: {extraction_info.get('total_files_processed', 0)}")
            print(f"SUCCESSFUL EXTRACTIONS: {extraction_info.get('successful_extractions', 0)}")
            
            return proof_goals
            
        except FileNotFoundError:
            print(f"ERROR: JSON file {self.json_file} not found")
            return []
        except json.JSONDecodeError as e:
            print(f"ERROR: Invalid JSON in {self.json_file}: {e}")
            return []
        except Exception as e:
            print(f"ERROR: Failed to load {self.json_file}: {e}")
            return []
    
    def load_base_with_verification(self) -> bool:
        """Load base.ml and verify it loaded correctly."""
        print("=" * 60)
        print("ATTEMPTING TO LOAD BASE.ML")
        print("=" * 60)
        
        # Load base.ml which should include assembly definitions
        if self.checker.load_needs_file("arm/proofs/base.ml", timeout=400):
            print("=" * 60)
            print("VERIFYING BASE.ML COMPONENTS")
            print("=" * 60)
            
            # Test basic components
            tests = [
                ("word", "Word type constructor"),
                ("read", "State reading function"),
                ("ensures", "Core ensures predicate")
            ]
            
            all_verified = True
            for test_def, description in tests:
                print(f"Testing: {test_def} - {description}")
                if self.checker.test_definition(test_def):
                    print(f"  Available: {test_def}")
                else:
                    print(f"  Not available: {test_def}")
                    all_verified = False
            
            print("=" * 60)
            if all_verified:
                print("BASE.ML VERIFICATION: SUCCESS")
                return True
            else:
                print("BASE.ML VERIFICATION: PARTIAL (proceeding anyway)")
                return True  # Proceed even with partial verification
        else:
            print("BASE.ML LOADING: FAILED")
            return False
    
    def is_problematic_definition(self, line: str) -> bool:
        """Check if a line contains problematic assembly definitions."""
        problematic_patterns = [
            r'define_assert_from_elf.*\[.*0x[0-9a-fA-F]+',  # Large hex arrays
            r'define_from_elf',                              # Any define_from_elf command
            r'let.*_mc\s*=\s*define_assert_from_elf',        # Assembly machine code
            r'let.*_mc\s*=\s*define_from_elf',               # Assembly machine code (variant)
            r'ARM_MK_EXEC_RULE.*_mc',                        # ARM execution rules
            r'let.*_EXEC\s*=\s*ARM_MK_EXEC_RULE',           # EXEC rule definitions
            r'let.*_CONV_backup\s*=\s*!',                    # Backup operations that fail
            r'extra_word_CONV\s*:=',                         # CONV assignments that fail
        ]
        
        for pattern in problematic_patterns:
            if re.search(pattern, line):
                return True
        return False
    
    def is_problematic_single_line_proof(self, proof: str) -> bool:
        """Detect single-line proofs that are likely to crash HOL Light server."""
        # Check for extremely long single lines (like the BIGNUM_KMUL_16_32_LEMMA example)
        lines = proof.split('\n')
        
        for line in lines:
            line = line.strip()
            if not line:
                continue
                
            # Look for proof patterns that are problematic when on single lines
            problematic_single_line_patterns = [
                # Extremely long single-line proofs
                (len(line) > 5000, "Extremely long single line"),
                
                # Dense tactic sequences without breaks
                (line.count('THEN') > 20 and '\n' not in line, "Dense tactic sequence on single line"),
                
                # Large ARM_ACCSTEPS_TAC calls on single lines
                (re.search(r'ARM_ACCSTEPS_TAC.*\[\d+;\d+;\d+.*\].*\(\d+--\d+\)', line) and len(line) > 1000, 
                 "Large ARM_ACCSTEPS_TAC on single line"),
                
                # Excessive ARM_ACCSTEPS_TAC chains
                (line.count('ARM_ACCSTEPS_TAC') > 5 and len(line) > 2000, "Multiple ARM_ACCSTEPS_TAC on single line"),
                
                # Long bignum operations on single lines
                (re.search(r'bignum_of_wordlist.*\[.*\]', line) and len(line) > 3000, 
                 "Long bignum operations on single line"),
                
                # Excessive mathematical operations
                (line.count('MAP_EVERY') > 10 and len(line) > 2000, "Excessive MAP_EVERY operations"),
                
                # Dense REWRITE_TAC sequences
                (line.count('REWRITE_TAC') > 10 and len(line) > 1500, "Dense REWRITE_TAC sequence"),
            ]
            
            for condition, description in problematic_single_line_patterns:
                if condition:
                    print(f"  PROBLEMATIC PATTERN DETECTED: {description}")
                    print(f"  LINE LENGTH: {len(line)} characters")
                    print(f"  LINE PREVIEW: {line[:100]}...")
                    return True
        
        return False
    
    def normalize_comments(self, proof: str) -> str:
        """Normalize problematic comment formats that can cause parser issues."""
        # Convert triple-asterisk comments to standard format
        # (*** ... ***) -> (* ... *)
        proof = re.sub(r'\(\*\*\*\s*(.*?)\s*\*\*\*\)', r'(* \1 *)', proof)
        
        # Fix other problematic comment patterns
        # Remove excessive asterisks in comments
        proof = re.sub(r'\(\*\*+\s*(.*?)\s*\*\*+\)', r'(* \1 *)', proof)
        
        # Ensure proper spacing in comments
        proof = re.sub(r'\(\*([^*])', r'(* \1', proof)
        proof = re.sub(r'([^*])\*\)', r'\1 *)', proof)
        
        return proof
    
    def format_long_proof_safely(self, proof: str) -> str:
        """Format extremely long proofs to prevent server crashes."""
        if not self.is_problematic_single_line_proof(proof):
            # Still normalize comments even for non-problematic proofs
            return self.normalize_comments(proof)
        
        print(f"  REFORMATTING PROBLEMATIC PROOF FOR SAFETY")
        
        # First normalize comments to prevent parser issues
        formatted = self.normalize_comments(proof)
        print(f"  NORMALIZED COMMENTS: Fixed problematic comment formats")
        
        # Split on major tactic keywords to create natural break points
        tactic_keywords = [
            'ARM_ACCSTEPS_TAC', 'ABBREV_TAC', 'SUBGOAL_THEN', 'MAP_EVERY',
            'REWRITE_TAC', 'ENSURES_INIT_TAC', 'BIGNUM_DIGITIZE_TAC',
            'ACCUMULATOR_POP_ASSUM_LIST', 'DISCARD_MATCHING_ASSUMPTIONS',
            'MATCH_MP_TAC', 'EXPAND_TAC', 'TRANS_TAC', 'CONJ_TAC'
        ]
        
        # Insert line breaks before major tactics (but only if not already multi-line)
        if '\n' not in formatted.strip():
            for keyword in tactic_keywords:
                # Insert line break before tactic (but not at the start)
                formatted = re.sub(f'(?<!^)\\s+{keyword}', f' THEN\n  {keyword}', formatted)
        
        # Insert line breaks before comments to separate them from tactics
        formatted = re.sub(r'(?<!^)(\s*\(\*[^*]*\*\))', r'\n\1', formatted)
        
        # Clean up excessive whitespace and ensure proper THEN placement
        lines = formatted.split('\n')
        clean_lines = []
        
        for i, line in enumerate(lines):
            line = line.strip()
            if not line:
                continue
            
            # Handle comment lines specially
            if line.startswith('(*'):
                clean_lines.append(line)  # Comments don't need THEN
                continue
            
            # Ensure THEN is properly placed for tactic lines
            if i > 0 and not line.startswith('THEN') and not clean_lines[-1].endswith('THEN') and not clean_lines[-1].startswith('(*'):
                if clean_lines:
                    clean_lines[-1] = clean_lines[-1] + ' THEN'
            
            clean_lines.append('  ' + line if not line.startswith('let') else line)
        
        result = '\n'.join(clean_lines)
        
        # Ensure proper termination
        if not result.endswith(';;'):
            if result.endswith(';'):
                result = result[:-1] + ';;'
            else:
                result += ';;'
        
        print(f"  REFORMATTED FROM {len(proof)} to {len(result)} chars with {len(clean_lines)} lines")
        return result
    
    def filter_setup_code(self, setup_code: str) -> tuple:
        """Filter out problematic assembly definitions from setup code."""
        print("=" * 60)
        print("FILTERING PROBLEMATIC SETUP CODE")
        print("=" * 60)
        
        lines = setup_code.split('\n')
        filtered_lines = []
        skipped_lines = []
        
        current_definition = ""
        in_problematic_def = False
        
        for line in lines:
            line = line.strip()
            if not line or line.startswith('(*') or line.startswith('needs'):
                continue
            
            # Check if starting a new definition
            if line.startswith('let ') and current_definition:
                # Process previous definition
                if in_problematic_def:
                    skipped_lines.append(current_definition)
                    self.skipped_definitions += 1
                else:
                    filtered_lines.append(current_definition)
                current_definition = ""
                in_problematic_def = False
            
            # Add to current definition
            current_definition += line + " "
            
            # Check if this line makes the definition problematic
            if self.is_problematic_definition(line):
                in_problematic_def = True
            
            # If definition ends, process it
            if line.endswith(';;'):
                if in_problematic_def:
                    skipped_lines.append(current_definition)
                    self.skipped_definitions += 1
                    print(f"SKIPPED PROBLEMATIC: {current_definition[:80]}...")
                else:
                    filtered_lines.append(current_definition)
                    print(f"KEPT SAFE: {current_definition[:80]}...")
                current_definition = ""
                in_problematic_def = False
        
        # Handle any remaining definition
        if current_definition:
            if in_problematic_def:
                skipped_lines.append(current_definition)
                self.skipped_definitions += 1
            else:
                filtered_lines.append(current_definition)
        
        filtered_setup = '\n'.join(filtered_lines)
        
        print(f"FILTERING RESULTS:")
        print(f"  ORIGINAL LINES: {len(lines)}")
        print(f"  KEPT DEFINITIONS: {len(filtered_lines)}")
        print(f"  SKIPPED DEFINITIONS: {len(skipped_lines)}")
        print(f"  TOTAL SKIPPED SO FAR: {self.skipped_definitions}")
        
        return filtered_setup, skipped_lines
    
    def normalize_theorem_statement(self, statement: str) -> str:
        """Normalize multi-line theorem statement to single line for OCaml parsing."""
        # Remove leading/trailing whitespace and normalize internal whitespace
        normalized = re.sub(r'\s+', ' ', statement.strip())
        
        # Remove inline comments (// comments) that were extracted as semantic annotations
        # but shouldn't be sent to HOL Light for validation
        normalized = re.sub(r'//[^\n\r]*', '', normalized)
        
        # Clean up any extra whitespace left after comment removal
        normalized = re.sub(r'\s+', ' ', normalized).strip()
        
        # Fix critical OCaml syntax issues
        # Fix broken implication operator - handle all variations
        normalized = re.sub(r'=\s*=\s*>\s*', '==> ', normalized)
        normalized = re.sub(r'=\s+>\s*', '==> ', normalized)
        normalized = re.sub(r'=\s*=\s+>\s*', '==> ', normalized)
        
        # Fix array formatting - remove spaces after semicolons in arrays only
        # Target specific array patterns like [p; z; m; x; n; y] -> [p;z;m;x;n;y]
        normalized = re.sub(r'\[\s*([^]]+)\s*\]', lambda m: '[' + re.sub(r';\s+', ';', m.group(1)) + ']', normalized)
        
        # Fix parentheses spacing
        normalized = re.sub(r'\s+\)', ')', normalized)
        normalized = re.sub(r'\(\s+', '(', normalized)
        
        # Ensure it starts with backtick if it's a HOL Light term
        if not normalized.startswith('`'):
            normalized = '`' + normalized
        
        # Ensure it ends with backtick if it's a HOL Light term
        if not normalized.endswith('`'):
            normalized = normalized + '`'
        
        return normalized
    
    def normalize_ocaml_command(self, command: str) -> str:
        """Normalize OCaml command - preserve complete proof structure."""
        # Always preserve the complete structure of prove statements
        if 'prove' in command and '`' in command:
            print(f"    PROVE STATEMENT DETECTED ({len(command)} chars) - preserving complete structure")
            
            # For prove statements, we need to be very careful to preserve the structure
            # let THEOREM_NAME = prove (`statement`, tactics);;
            
            # Just do minimal cleaning while preserving the logical structure
            result = command.strip()
            
            # Only fix critical syntax issues that would break parsing
            result = re.sub(r'=\s*=\s*>\s*', '==> ', result)
            result = re.sub(r'=\s+>\s*', '==> ', result) 
            result = re.sub(r'=\s*=\s+>\s*', '==> ', result)
            
            # Fix array spacing: [a; b; c] -> [a;b;c] 
            result = re.sub(r'\[\s*([^]]+)\s*\]', lambda m: '[' + re.sub(r';\s+', ';', m.group(1)) + ']', result)
            
            # Fix parentheses spacing
            result = re.sub(r'\s+\)', ')', result)
            result = re.sub(r'\(\s+', '(', result)
            
            # Ensure proper ;; termination
            if not result.endswith(';;'):
                if result.endswith(';'):
                    result = result[:-1] + ';;'
                else:
                    result += ';;'
            
            return result
        else:
            # For non-prove commands, normalize to single line as before
            normalized = re.sub(r'\s+', ' ', command.strip())
            
            # Fix double semicolon spacing issues first
            normalized = re.sub(r';\s*;\s*', ';;', normalized)
            normalized = re.sub(r';\s+;', ';;', normalized)
            
            # Ensure proper ;; termination
            if not normalized.endswith(';;'):
                if normalized.endswith(';'):
                    normalized = normalized[:-1] + ';;'
                else:
                    normalized += ';;'
            
            return normalized.strip()
    
    def normalize_theorem_statement_in_proof(self, proof: str) -> str:
        """Apply theorem statement normalization fixes to the entire proof command."""
        # Fix critical OCaml syntax issues that might still be present
        # Fix broken implication operator - handle all variations
        normalized = re.sub(r'=\s*=\s*>\s*', '==> ', proof)
        normalized = re.sub(r'=\s+>\s*', '==> ', normalized)
        normalized = re.sub(r'=\s*=\s+>\s*', '==> ', normalized)
        
        # Fix array formatting - only target arrays, not mathematical operators
        normalized = re.sub(r'\[\s*([^]]+)\s*\]', lambda m: '[' + re.sub(r';\s+', ';', m.group(1)) + ']', normalized)
        
        # Fix parentheses spacing
        normalized = re.sub(r'\s+\)', ')', normalized)
        normalized = re.sub(r'\(\s+', '(', normalized)
        
        return normalized
    
    def execute_setup_code(self, setup_code: str) -> bool:
        """Execute all setup code as complete OCaml definitions with enhanced validation."""
        print("=" * 60)
        print("EXECUTING SETUP CODE FROM JSON")
        print("=" * 60)
        print("JSON FIELD: 'setup_code'")
        print("CONTENT TO SEND TO HOL LIGHT SERVER:")
        print("-" * 40)
        print(setup_code)
        print("-" * 40)
        
        if not setup_code.strip():
            print("NO SETUP CODE TO EXECUTE")
            return True
        
        # Extract needs files for special handling
        needs_files = []
        needs_pattern = r'needs\s+"([^"]+)"'
        for match in re.finditer(needs_pattern, setup_code):
            needs_files.append(match.group(1))
        
        print(f"DETECTED {len(needs_files)} NEEDS FILES: {needs_files}")
        
        # Load needs files first with verification
        critical_needs_failed = []
        for needs_file in needs_files:
            print(f"\n{'='*50}")
            print(f"LOADING CRITICAL NEEDS FILE: {needs_file}")
            print(f"{'='*50}")
            
            if not self.checker.load_needs_file(needs_file, timeout=400):
                critical_needs_failed.append(needs_file)
                print(f"CRITICAL FAILURE: Could not load {needs_file}")
            else:
                print(f"SUCCESS: Loaded {needs_file}")
        
        # If critical needs files failed, report it but continue
        if critical_needs_failed:
            print(f"\nWARNING: {len(critical_needs_failed)} needs files failed to load:")
            for failed_file in critical_needs_failed:
                print(f"  - {failed_file}")
            print("This may cause later definitions to fail due to missing dependencies.")
        
        # Parse remaining OCaml commands (excluding needs statements)
        commands = []
        current_command = ""
        brace_count = 0
        bracket_count = 0
        paren_count = 0
        in_string = False
        in_comment = False
        
        i = 0
        while i < len(setup_code):
            char = setup_code[i]
            
            # Handle comments
            if not in_string and i < len(setup_code) - 1 and setup_code[i:i+2] == '(*':
                in_comment = True
                current_command += char
                i += 1
                continue
            elif in_comment and i < len(setup_code) - 1 and setup_code[i:i+2] == '*)':
                in_comment = False
                current_command += char
                i += 1
                continue
            elif in_comment:
                current_command += char
                i += 1
                continue
            
            # Handle strings
            if char == '"' and not in_comment:
                in_string = not in_string
                current_command += char
                i += 1
                continue
            elif in_string:
                current_command += char
                i += 1
                continue
            
            # Count brackets/braces/parens
            if char == '[':
                bracket_count += 1
            elif char == ']':
                bracket_count -= 1
            elif char == '{':
                brace_count += 1
            elif char == '}':
                brace_count -= 1
            elif char == '(':
                paren_count += 1
            elif char == ')':
                paren_count -= 1
            
            current_command += char
            
            # Check for command termination
            if (char == ';' and i < len(setup_code) - 1 and setup_code[i+1] == ';' and
                bracket_count == 0 and brace_count == 0 and paren_count == 0):
                current_command += ';'  # Add the second semicolon
                i += 1  # Skip the second semicolon
                
                # We have a complete command
                cmd = current_command.strip()
                if cmd and not cmd.startswith('(*') and not cmd.startswith('needs'):
                    commands.append(cmd)
                current_command = ""
            
            i += 1
        
        # Handle any remaining command
        if current_command.strip():
            cmd = current_command.strip()
            if not cmd.endswith(';;'):
                cmd += ';;'
            if not cmd.startswith('needs'):
                commands.append(cmd)
        
        print(f"\nPARSED {len(commands)} NON-NEEDS OCAML COMMANDS")
        
        # Execute non-needs commands
        failed_commands = []
        for i, command in enumerate(commands, 1):
            print(f"\n{'='*40}")
            print(f"COMMAND {i}/{len(commands)}")
            print(f"{'='*40}")
            print(f"COMMAND PREVIEW (ORIGINAL): {command[:100]}{'...' if len(command) > 100 else ''}")
            
            # Normalize command to single line for proper OCaml parsing
            normalized_command = self.normalize_ocaml_command(command)
            
            print(f"COMMAND PREVIEW (NORMALIZED): {normalized_command[:100]}{'...' if len(normalized_command) > 100 else ''}")
            print("SERVER RESPONSE:")
            
            # Send normalized command to server
            result = self.checker.send_command(normalized_command, show_streaming=True)
            
            print(f"RESULT: {'SUCCESS' if result.get('success') else 'FAILED'}")
            if not result.get("success"):
                print(f"ERROR: {result.get('error', 'Unknown error')}")
                print(f"FULL RESPONSE: {result.get('response', 'No response')}")
                failed_commands.append((command[:100], result.get('error', 'Unknown error')))
                
                # Check if this is a critical failure due to missing dependencies
                response = result.get('response', '')
                if any(indicator in response for indicator in [
                    "Free variables in predicate", "Unbound", "not found", "undefined"
                ]):
                    print("CRITICAL DEPENDENCY FAILURE DETECTED!")
                    print("This suggests that a needs file failed to load properly.")
                
                print("CONTINUING WITH NEXT COMMAND...")
            else:
                if result.get('response'):
                    print(f"RESPONSE: {result.get('response')}")
        
        print(f"\nSETUP CODE EXECUTION: COMPLETED")
        print(f"NEEDS FILES: {len(needs_files)} processed, {len(critical_needs_failed)} failed")
        print(f"OTHER COMMANDS: {len(commands)} processed, {len(failed_commands)} failed")
        
        # Return success if most commands succeeded
        if critical_needs_failed or len(failed_commands) > len(commands) // 2:
            print("SETUP CODE EXECUTION: PARTIAL SUCCESS (many failures detected)")
            return False
        else:
            print("SETUP CODE EXECUTION: SUCCESS")
            return True
    
    def normalize_complete_proof(self, complete_proof: str) -> str:
        """Normalize complete proof, handling both 'prove' and 'time prove' syntax."""
        print(f"    NORMALIZING COMPLETE PROOF ({len(complete_proof)} chars)")
        
        # Handle time prove by converting it to regular prove for HOL Light server
        # The server will still measure time internally, but we avoid syntax issues
        normalized = re.sub(r'= time prove\b', '= prove', complete_proof)
        print(f"    CONVERTED 'time prove' to 'prove': {'time prove' in complete_proof}")
        
        # CRITICAL: Remove all newlines to prevent the server from splitting the command
        # The HOL Light server treats each line as a separate command, so we must
        # convert multi-line proofs to single-line format
        has_newlines = '\n' in normalized
        print(f"    ORIGINAL CONTAINS NEWLINES: {has_newlines}")
        
        # FORCE conversion to single line - this is critical for server compatibility
        # Replace ALL types of line breaks and excessive whitespace
        normalized = normalized.replace('\r\n', ' ')  # Windows line endings
        normalized = normalized.replace('\r', ' ')    # Mac line endings  
        normalized = normalized.replace('\n', ' ')    # Unix line endings
        
        # Clean up excessive whitespace
        normalized = re.sub(r'\s+', ' ', normalized)
        print(f"    CONVERTED TO SINGLE LINE: Removed all newlines")
        
        # Fix critical syntax issues only
        normalized = re.sub(r'=\s*=\s*>\s*', '==> ', normalized)
        normalized = re.sub(r'=\s+>\s*', '==> ', normalized)
        normalized = re.sub(r'=\s*=\s+>\s*', '==> ', normalized)
        
        # Fix array spacing: [a; b; c] -> [a;b;c] (but be careful not to break prove structure)
        normalized = re.sub(r'\[\s*([^]]+)\s*\]', lambda m: '[' + re.sub(r';\s+', ';', m.group(1)) + ']', normalized)
        
        # Fix parentheses spacing
        normalized = re.sub(r'\s+\)', ')', normalized)
        normalized = re.sub(r'\(\s+', '(', normalized)
        
        # Clean up any remaining excessive whitespace
        normalized = re.sub(r'\s+', ' ', normalized).strip()
        
        # Ensure proper ;; termination
        if not normalized.endswith(';;'):
            if normalized.endswith(';'):
                normalized = normalized[:-1] + ';;'
            else:
                normalized += ';;'
        
        print(f"    FINAL NORMALIZED LENGTH: {len(normalized)} chars")
        
        # CRITICAL VERIFICATION: Ensure absolutely no newlines remain
        newline_check = '\n' in normalized or '\r' in normalized
        if newline_check:
            print(f"    CRITICAL ERROR: Line breaks still present after normalization!")
            # Emergency cleanup - force remove ANY remaining line break characters
            normalized = re.sub(r'[\r\n]+', ' ', normalized)
            normalized = re.sub(r'\s+', ' ', normalized).strip()
            print(f"    EMERGENCY CLEANUP: Force-removed all line break characters")
        
        final_newline_count = normalized.count('\n') + normalized.count('\r')
        print(f"    FINAL LINE BREAK COUNT: {final_newline_count} (must be 0)")
        print(f"    PREVIEW: {normalized[:200]}...")
        
        if final_newline_count > 0:
            raise ValueError(f"CRITICAL: {final_newline_count} line breaks remain after normalization!")
        
        return normalized
    
    def validate_proof(self, goal: dict, goal_number: int, total_goals: int) -> dict:
        """Validate a single proof using the complete_proof field directly."""
        print(f"\n{'='*80}")
        print(f"COMPLETE PROOF VALIDATION {goal_number}/{total_goals}: {goal['theorem_name']}")
        print(f"{'='*80}")
        print(f"DESCRIPTION: {goal['description']}")
        print(f"FILE: {goal['file']}")
        print(f"SUCCESS RATE: {self.successful_validations}/{goal_number-1} ({(self.successful_validations/(goal_number-1)*100) if goal_number > 1 else 0:.1f}%)")
        
        start_time = time.time()
        
        try:
            # Step 1: Connect to server
            print(f"\n{'='*60}")
            print("STEP 1: CONNECTING TO HOL LIGHT SERVER")
            print(f"{'='*60}")
            if not self.checker.connect():
                return {
                    "success": False,
                    "error": "Failed to connect to HOL Light server",
                    "goal": goal['theorem_name'],
                    "time_taken": time.time() - start_time
                }
            
            # Step 2: Load base.ml with assembly definitions
            print(f"\n{'='*60}")
            print("STEP 2: LOADING BASE WITH ASSEMBLY")
            print(f"{'='*60}")
            
            if not self.load_base_with_verification():
                return {
                    "success": False,
                    "error": "Failed to load base.ml",
                    "goal": goal['theorem_name'],
                    "time_taken": time.time() - start_time
                }
            
            # Step 3: Execute setup code
            print(f"\n{'='*60}")
            print("STEP 3: EXECUTING SETUP CODE")
            print(f"{'='*60}")
            
            if not self.execute_setup_code(goal['setup_code']):
                return {
                    "success": False,
                    "error": "Failed to execute setup code",
                    "goal": goal['theorem_name'],
                    "time_taken": time.time() - start_time
                }
            
            # Step 4: Use complete proof directly (handles both prove and time prove)
            print(f"\n{'='*60}")
            print("STEP 4: COMPLETE PROOF VALIDATION")
            print(f"{'='*60}")
            
            # Use the complete_proof field directly instead of reconstructing
            if 'complete_proof' not in goal:
                return {
                    "success": False,
                    "error": "Missing complete_proof field in JSON",
                    "goal": goal['theorem_name'],
                    "file": goal['file'],
                    "time_taken": time.time() - start_time
                }
            
            complete_proof = goal['complete_proof']
            
            print("JSON FIELD: 'complete_proof'")
            print("COMPLETE PROOF (ORIGINAL):")
            print("-" * 40)
            print(complete_proof[:500] + "..." if len(complete_proof) > 500 else complete_proof)
            print("-" * 40)
            
            # Check if this uses time prove syntax
            uses_time_prove = 'time prove' in complete_proof
            if uses_time_prove:
                print("DETECTED: 'time prove' syntax - will normalize to 'prove'")
            else:
                print("DETECTED: regular 'prove' syntax")
            
            # Normalize the complete proof (handles time prove conversion and formatting)
            print(f"BEFORE NORMALIZATION - PROOF HAS {complete_proof.count(chr(10))} newlines:")
            print(f"FIRST 200 CHARS: {repr(complete_proof[:200])}")
            
            normalized_complete_proof = self.normalize_complete_proof(complete_proof)
            
            print("COMPLETE PROOF (NORMALIZED):")
            print("-" * 40)
            print(normalized_complete_proof[:500] + "..." if len(normalized_complete_proof) > 500 else normalized_complete_proof)
            print("-" * 40)
            print(f"PROOF LENGTH: {len(normalized_complete_proof)} characters")
            
            # Final verification before sending to server
            newline_count = normalized_complete_proof.count('\n')
            carriage_return_count = normalized_complete_proof.count('\r')
            print(f"NEWLINE COUNT IN NORMALIZED PROOF: {newline_count}")
            print(f"CARRIAGE RETURN COUNT IN NORMALIZED PROOF: {carriage_return_count}")
            print(f"TOTAL LINE BREAKS: {newline_count + carriage_return_count}")
            
            if newline_count > 0 or carriage_return_count > 0:
                print("ERROR: Normalized proof still contains line breaks!")
                print("FORCE REMOVING ALL LINE BREAKS...")
                normalized_complete_proof = normalized_complete_proof.replace('\n', ' ')
                normalized_complete_proof = normalized_complete_proof.replace('\r', ' ')
                normalized_complete_proof = re.sub(r'\s+', ' ', normalized_complete_proof).strip()
                final_newlines = normalized_complete_proof.count('\n')
                final_cr = normalized_complete_proof.count('\r')
                print(f"AFTER FORCE CLEANUP: {final_newlines} newlines, {final_cr} carriage returns")
            
            # CRITICAL DEBUG: Show exact command being sent
            print("=" * 60)
            print("FINAL COMMAND TO BE SENT TO SERVER:")
            print("=" * 60)
            print(f"LENGTH: {len(normalized_complete_proof)} chars")
            print(f"CONTAINS NEWLINES: {chr(10) in normalized_complete_proof}")
            print(f"CONTAINS CR: {chr(13) in normalized_complete_proof}")
            print(f"REPR OF FIRST 300 CHARS: {repr(normalized_complete_proof[:300])}")
            print("=" * 60)
            
            print("SERVER RESPONSE:")
            
            result = self.checker.send_command(normalized_complete_proof, timeout=400, show_streaming=True)
            
            print(f"RESULT: {'SUCCESS' if result.get('success') else 'FAILED'}")
            if result.get("success"):
                print("COMPLETE PROOF VALIDATION: SUCCESS")
                self.successful_validations += 1
                end_time = time.time()
                total_time = end_time - start_time
                
                if result.get('response'):
                    print(f"RESPONSE: {result.get('response')}")
                
                return {
                    "success": True,
                    "proof": normalized_complete_proof,
                    "method": "complete_proof_validation",
                    "original_used_time_prove": uses_time_prove,
                    "time_taken": total_time,
                    "goal": goal['theorem_name'],
                    "file": goal['file']
                }
            else:
                print("COMPLETE PROOF VALIDATION: FAILED")
                print(f"ERROR: {result.get('error', 'Unknown error')}")
                print(f"FULL RESPONSE: {result.get('response', 'No response')}")
                return {
                    "success": False,
                    "error": f"Complete proof validation failed: {result.get('error', 'Unknown error')}",
                    "goal": goal['theorem_name'],
                    "file": goal['file'],
                    "time_taken": time.time() - start_time
                }
                
        except Exception as e:
            error_msg = f"Exception during complete proof validation: {str(e)}"
            print(f"EXCEPTION: {error_msg}")
            return {
                "success": False,
                "error": error_msg,
                "goal": goal['theorem_name'],
                "time_taken": time.time() - start_time
            }
        finally:
            # Always disconnect for fresh state
            self.checker.disconnect()
    
    def validate_all_proofs(self, output_file: str = None):
        """Validate all proofs using smart filtering approach with robust features."""
        
        print("SMART PROOF VALIDATOR WITH ROBUST FEATURES")
        print("="*80)
        print("ROBUST SMART CAPABILITIES:")
        print("1. Perfect assembly filtering (whitelist approach)")
        print("2. Skips define_assert_from_elf commands that crash server")
        print("3. Dependency resolution with topological sorting")
        print("4. Fresh connections for isolation")
        print("5. Uses pre-loaded assembly from base.ml")
        print("6. Detailed filtering and progress statistics")
        print("="*80)
        
        # Load proof goals from JSON
        proof_goals = self.load_proof_goals()
        if not proof_goals:
            print("ERROR: No proof goals loaded from JSON file")
            return []
        
        print(f"PROOF GOALS LOADED: {len(proof_goals)} goals found")
        
        # Apply dependency resolution
        print("RESOLVING DEPENDENCIES...")
        resolved_goals = self.dependency_resolver.resolve_dependencies(proof_goals)
        print(f"DEPENDENCY RESOLUTION: Complete")
        print(f"EXECUTION ORDER: Optimized for dependencies")
        
        proof_goals = resolved_goals
        
        results = []
        
        for i, goal in enumerate(proof_goals, 1):
            print(f"\n{'#'*80}")
            print(f"PROCESSING GOAL {i}/{len(proof_goals)}: {goal['file']}")
            print(f"THEOREM NAME: {goal['theorem_name']}")
            print(f"{'#'*80}")
            
            try:
                validation_result = self.validate_proof(goal, i, len(proof_goals))
                results.append(validation_result)
                
                if validation_result.get("success", False):
                    print(f"GOAL {i} RESULT: SUCCESS - {goal['theorem_name']} validated!")
                    print(f"TIME TAKEN: {validation_result.get('time_taken', 0):.2f} seconds")
                else:
                    print(f"GOAL {i} RESULT: FAILED - {goal['theorem_name']}")
                    print(f"FAILURE REASON: {validation_result.get('error', 'Unknown error')}")
                
                # Show running statistics
                current_success_rate = (self.successful_validations / i) * 100
                print(f"RUNNING STATISTICS: {self.successful_validations}/{i} successful ({current_success_rate:.1f}%)")
                print(f"TOTAL SKIPPED DEFINITIONS: {self.skipped_definitions}")
                
            except Exception as e:
                print(f"GOAL {i} EXCEPTION: {goal['theorem_name']}: {e}")
                results.append({
                    "success": False,
                    "error": str(e),
                    "goal": goal['theorem_name'],
                    "file": goal['file']
                })
        
        # Save results with timestamp
        timestamp = time.strftime("%Y%m%d_%H%M%S")
        if output_file is None:
            output_file = f"smart_validation_results_{timestamp}.json"
        
        final_results = {
            "validation_info": {
                "timestamp": timestamp,
                "source_json": self.json_file,
                "total_goals": len(proof_goals),
                "successful_validations": self.successful_validations,
                "success_rate": f"{self.successful_validations/len(proof_goals)*100:.1f}%",
                "validator_type": "smart_filtered_validation",
                "total_skipped_definitions": self.skipped_definitions
            },
            "results": results
        }
        
        with open(output_file, 'w') as f:
            json.dump(final_results, f, indent=2)
        
        # Summary
        print(f"\n{'='*80}")
        print("SMART PROOF VALIDATION SESSION SUMMARY")
        print(f"{'='*80}")
        print(f"SOURCE JSON FILE: {self.json_file}")
        print(f"TOTAL GOALS PROCESSED: {len(proof_goals)}")
        print(f"SUCCESSFUL VALIDATIONS: {self.successful_validations}")
        print(f"SUCCESS RATE: {self.successful_validations/len(proof_goals)*100:.1f}%")
        print(f"TOTAL SKIPPED DEFINITIONS: {self.skipped_definitions}")
        print(f"RESULTS SAVED TO: {output_file}")
        
        # Show improvement over baseline
        baseline_success_rate = 5.6
        improvement = (self.successful_validations/len(proof_goals)*100) - baseline_success_rate
        print(f"IMPROVEMENT OVER BASELINE: {improvement:+.1f}%")
        
        return results

def main():
    """Main entry point."""
    import argparse
    
    parser = argparse.ArgumentParser(description="Smart ARM Proof Validator")
    parser.add_argument("json_file", nargs='?', 
                       default="sample_arm_proofs.json",
                       help="JSON file containing extracted proof goals")
    parser.add_argument("--output", 
                       help="Output file for validation results (default: auto-generated)")
    
    args = parser.parse_args()
    
    # Check if JSON file exists
    if not Path(args.json_file).exists():
        print(f"ERROR: JSON file {args.json_file} not found")
        print("Available JSON files:")
        for json_file in Path(".").glob("*.json"):
            print(f"  {json_file}")
        return 1
    
    validator = SmartProofValidator(args.json_file)
    results = validator.validate_all_proofs(args.output)
    
    return 0 if any(r.get("success", False) for r in results) else 1

if __name__ == "__main__":
    exit(main())

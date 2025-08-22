#!/usr/bin/env python3
"""
Automated Proof Builder for s2n-bignum Theorems

This script processes extracted theorems from JSON files and automatically
builds/validates proofs using HOL Light, based on the hol_demo.py structure.
"""

import sys
import json
import os
import argparse
import time
import re
from pathlib import Path
from typing import Dict, List, Any, Optional

# Add paths for LLM tactic prover (from demo_isolated)
sys.path.append('demo_isolated')

import socket

class HOLLightChecker:
    """HOL Light server communication (from smart_proof_validator.py)."""
    
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
        """Send command to HOL Light server and navigate by server outputs."""
        if not self.connected:
            return {"success": False, "error": "Not connected to server"}
        
        # CRITICAL: Verify command is single line before sending
        newline_count = command.count('\n') + command.count('\r')
        if newline_count > 0:
            print(f"    CRITICAL ERROR: Command contains {newline_count} line breaks!")
            # Emergency normalization
            command = command.replace('\r\n', ' ').replace('\r', ' ').replace('\n', ' ')
            command = re.sub(r'\s+', ' ', command).strip()
        
        # Use a generous timeout only as a safety net (10 minutes)
        safety_timeout = 600
        if timeout is None:
            timeout = safety_timeout
        
        try:
            # Send command - add only a single newline for server protocol
            full_command = command + '\n'
            
            # Final verification before sending
            full_command_newlines = full_command.count('\n')
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

def check_server():
    """Check if HOL Light server is accessible."""
    try:
        checker = HOLLightChecker()
        if checker.connect():
            print("+ HOL Light server is running and accessible")
            checker.disconnect()
            return True
        else:
            print("- Failed to connect to HOL Light server")
            print("  Make sure the server is running on localhost:2012")
            return False
    except Exception as e:
        print(f"- Server check failed: {e}")
        return False

def load_base_with_verification() -> bool:
    """Load base.ml and verify it loaded correctly (like smart_proof_validator.py)."""
    try:
        checker = HOLLightChecker(timeout=400)
        if not checker.connect():
            print("- Cannot connect to server for base loading")
            return False
        
        print("=" * 60)
        print("ATTEMPTING TO LOAD BASE.ML")
        print("=" * 60)
        
        # Load base.ml using loadt (not needs) - following smart_proof_validator.py approach
        base_file = "arm/proofs/base.ml"
        command = f'loadt "{base_file}";;'
        print(f"Loading: {base_file}")
        print("Using loadt command (following smart_proof_validator.py approach)")
        print("This may take several minutes...")
        
        # Use streaming output for base.ml loading  
        result = checker.send_command(command, timeout=400, show_streaming=True)
        
        # Enhanced success detection for loadt files (from smart_proof_validator.py)
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
            print("=" * 60)
            print("VERIFYING BASE.ML COMPONENTS")
            print("=" * 60)
            
            # Test basic components that should be available
            test_definitions = [
                ("word", "Word type constructor"),
                ("read", "State reading function"), 
                ("ensures", "Core ensures predicate"),
                ("bignum_of_wordlist", "Bignum conversion function"),
                ("val", "Word value extraction function")
            ]
            
            all_verified = True
            for test_def, description in test_definitions:
                print(f"Testing: {test_def} - {description}")
                test_result = checker.send_command(f"{test_def};;", timeout=10)
                
                if test_result.get("success", False):
                    response = test_result.get("response", "")
                    if not any(err in response for err in ["Unbound", "not found", "undefined", "Exception", "Error"]):
                        print(f"  + Available: {test_def}")
                    else:
                        print(f"  - Error with {test_def}: {response}")
                        all_verified = False
                else:
                    print(f"  - Not available: {test_def}")
                    all_verified = False
            
            print("=" * 60)
            if all_verified:
                print("BASE.ML VERIFICATION: SUCCESS")
            else:
                print("BASE.ML VERIFICATION: PARTIAL (proceeding anyway)")
                
            checker.disconnect()
            return True
        else:
            print("BASE.ML LOADING: FAILED")
            print(f"Error: {result.get('error', 'Unknown error')}")
            print(f"Full response: {response}")
            checker.disconnect()
            return False
            
    except Exception as e:
        print(f"- Base loading failed: {e}")
        return False

def execute_setup_code_methodically(setup_commands: List[str]) -> bool:
    """Execute setup code with methodical approach (like smart_proof_validator.py)."""
    if not setup_commands:
        print("No additional setup commands provided")
        return True
        
    try:
        checker = HOLLightChecker(timeout=400)
        if not checker.connect():
            print("- Cannot connect to server for setup")
            return False
        
        print("=" * 60)
        print("EXECUTING ADDITIONAL SETUP CODE")
        print("=" * 60)
        print("SETUP COMMANDS TO EXECUTE:")
        print("-" * 40)
        for i, cmd in enumerate(setup_commands, 1):
            if cmd.strip() and not cmd.startswith('#'):
                print(f"[{i}] {cmd}")
        print("-" * 40)
        
        failed_commands = []
        
        for i, command in enumerate(setup_commands, 1):
            if not command.strip() or command.startswith('#'):
                continue
                
            print(f"\n{'='*50}")
            print(f"SETUP COMMAND {i}/{len(setup_commands)}")
            print(f"{'='*50}")
            print(f"COMMAND: {command}")
            
            # Normalize the command for proper OCaml parsing (single line)
            normalized_command = command.replace('\r\n', ' ').replace('\r', ' ').replace('\n', ' ')
            normalized_command = re.sub(r'\s+', ' ', normalized_command).strip()
            
            # Add ;; if not present
            if not normalized_command.endswith(';;'):
                normalized_command += ';;'
            
            # Set appropriate timeout and handle different command types
            if 'loadt' in normalized_command or 'needs' in normalized_command:
                timeout = 400
                print("    Using extended timeout for file loading...")
                show_streaming = True
            elif any(lexer_cmd in normalized_command for lexer_cmd in ['unset_jrh_lexer', 'set_jrh_lexer']):
                timeout = 30
                print("    Lexer command detected...")
                show_streaming = False
            else:
                timeout = 60
                show_streaming = False
            
            print(f"NORMALIZED COMMAND: {normalized_command}")
            print("SERVER RESPONSE:")
            result = checker.send_command(normalized_command, timeout=timeout, show_streaming=show_streaming)
            
            print(f"RESULT: {'SUCCESS' if result.get('success') else 'FAILED'}")
            
            if result.get("success", False):
                response = result.get('response', '')
                if response:
                    print(f"RESPONSE: {response}")
                print("+ Command executed successfully")
            else:
                error_msg = result.get('error', 'Unknown error')
                print(f"- ERROR: {error_msg}")
                print(f"FULL RESPONSE: {result.get('response', 'No response')}")
                failed_commands.append((command[:100], error_msg))
                
                # Check if this is a critical failure
                response = result.get('response', '')
                if any(indicator in response for indicator in [
                    "Free variables in predicate", "Unbound", "not found", "undefined"
                ]):
                    print("CRITICAL DEPENDENCY FAILURE DETECTED!")
                    print("This suggests missing dependencies or failed imports.")
                
                print("CONTINUING WITH NEXT COMMAND...")
        
        checker.disconnect()
        
        print(f"\n{'='*60}")
        print("SETUP CODE EXECUTION COMPLETED")
        print(f"{'='*60}")
        print(f"TOTAL COMMANDS: {len([c for c in setup_commands if c.strip() and not c.startswith('#')])}")
        print(f"FAILED COMMANDS: {len(failed_commands)}")
        
        if failed_commands:
            print("\nFAILED COMMANDS:")
            for cmd, error in failed_commands:
                print(f"  - {cmd}: {error}")
        
        # Return success if most commands succeeded
        total_commands = len([c for c in setup_commands if c.strip() and not c.startswith('#')])
        if len(failed_commands) > total_commands // 2:
            print("SETUP EXECUTION: PARTIAL SUCCESS (many failures detected)")
            return False
        else:
            print("SETUP EXECUTION: SUCCESS")
            return True
        
    except Exception as e:
        print(f"- Setup execution failed: {e}")
        return False

def setup_ocaml_environment_methodically(setup_commands: List[str]) -> bool:
    """Complete methodical setup process (like smart_proof_validator.py)."""
    print("s2n-bignum METHODICAL SETUP PROCESS")
    print("="*80)
    print("METHODICAL SETUP CAPABILITIES:")
    print("1. Load base.ml with verification of critical components")
    print("2. Execute additional setup commands with detailed logging")
    print("3. Verify definitions are available after loading")
    print("4. Show streaming output for long operations")
    print("5. Handle timeouts and errors gracefully")
    print("="*80)
    
    # Step 1: Load base.ml with verification
    print(f"\n{'='*60}")
    print("STEP 1: LOADING BASE WITH VERIFICATION")
    print(f"{'='*60}")
    
    if not load_base_with_verification():
        print("- Failed to load base.ml - this is critical for theorem proving")
        return False
    
    # Step 2: Execute additional setup commands if provided
    if setup_commands:
        print(f"\n{'='*60}")
        print("STEP 2: EXECUTING ADDITIONAL SETUP")
        print(f"{'='*60}")
        
        if not execute_setup_code_methodically(setup_commands):
            print("! Additional setup had failures, but continuing...")
            # Don't fail completely - base.ml is more critical
    
    print(f"\n{'='*60}")
    print("METHODICAL SETUP COMPLETED")
    print(f"{'='*60}")
    print("+ Environment ready for LLM theorem proving")
    
    return True

def normalize_theorem_statement(statement: str) -> str:
    """Normalize multi-line theorem statement to single line (like smart_proof_validator.py)."""
    # CRITICAL: Remove all newlines to prevent the server from splitting the command
    # The HOL Light server treats each line as a separate command
    
    print(f"    Normalizing theorem statement ({len(statement)} chars)")
    print(f"    Original newlines: {statement.count(chr(10))}")
    
    # Force conversion to single line
    normalized = statement.replace('\r\n', ' ')  # Windows line endings
    normalized = normalized.replace('\r', ' ')    # Mac line endings  
    normalized = normalized.replace('\n', ' ')    # Unix line endings
    
    # Clean up excessive whitespace
    normalized = re.sub(r'\s+', ' ', normalized).strip()
    
    # Fix critical OCaml syntax issues
    normalized = re.sub(r'=\s*=\s*>\s*', '==> ', normalized)
    normalized = re.sub(r'=\s+>\s*', '==> ', normalized)
    normalized = re.sub(r'=\s*=\s+>\s*', '==> ', normalized)
    
    # Fix array formatting: [a; b; c] -> [a;b;c]
    normalized = re.sub(r'\[\s*([^]]+)\s*\]', lambda m: '[' + re.sub(r';\s+', ';', m.group(1)) + ']', normalized)
    
    # Fix parentheses spacing
    normalized = re.sub(r'\s+\)', ')', normalized)
    normalized = re.sub(r'\(\s+', '(', normalized)
    
    # Ensure proper backtick formatting for HOL Light terms
    if not normalized.startswith('`'):
        normalized = '`' + normalized
    if not normalized.endswith('`'):
        normalized = normalized + '`'
    
    # CRITICAL VERIFICATION: Ensure absolutely no newlines remain
    final_newlines = normalized.count('\n') + normalized.count('\r')
    if final_newlines > 0:
        print(f"    CRITICAL ERROR: {final_newlines} line breaks still present!")
        # Emergency cleanup
        normalized = re.sub(r'[\r\n]+', ' ', normalized)
        normalized = re.sub(r'\s+', ' ', normalized).strip()
        print(f"    Emergency cleanup applied")
    
    print(f"    Normalized to single line ({len(normalized)} chars)")
    return normalized

def prove_theorem_with_llm(theorem_statement: str, description: str = "", context: str = "", file_name: str = "") -> Dict[str, Any]:
    """Generate proof for theorem using LLM (like hol_demo.py)."""
    try:
        from llm_tactic_prover import LLMTacticProver
        
        # CRITICAL: Normalize theorem statement to single line first
        normalized_statement = normalize_theorem_statement(theorem_statement)
        
        prover = LLMTacticProver()
        
        print(f"    Using LLM to generate proof...")
        
        # Build context from file name and description
        full_context = ""
        if file_name:
            full_context += f"Source file: {file_name}\n"
        if description:
            full_context += f"Description: {description}\n"
        if context:
            full_context += f"Additional context: {context}\n"
        
        # Use LLM to generate proof with normalized statement (like hol_demo.py)
        result = prover.prove_theorem(normalized_statement, full_context.strip(), description)
        
        success = result.get("success", False)
        return {
            "success": success,
            "error": result.get("error") if not success else None,
            "proof": result.get("proof", ""),
            "tactic_used": result.get("tactic_used", "unknown"),
            "reasoning": result.get("reasoning", ""),
            "llm_confidence": result.get("llm_confidence", 0.0),
            "total_attempts": result.get("total_attempts", 1),
            "time_taken": result.get("time_taken", 0),
            "generated_proof": True,
            "normalized_statement": normalized_statement
        }
        
    except Exception as e:
        return {"success": False, "error": str(e), "generated_proof": False}

def filter_theorems_by_classification(theorems: List[Dict[str, Any]], 
                                     classification: str) -> List[Dict[str, Any]]:
    """Filter theorems by their classification."""
    filtered = []
    for theorem in theorems:
        # Check if theorem has classification field
        if 'classification' in theorem:
            if theorem['classification'] == classification:
                filtered.append(theorem)
        else:
            # If no classification field, try to classify based on statement
            theorem_name = theorem.get('theorem_name', '')
            theorem_statement = theorem.get('theorem_statement', '')
            
            # Simple classification logic (based on filter_theorems.py)
            statement_lower = theorem_statement.lower()
            
            if classification == 'bitvector operations':
                bitvector_patterns = ['word_', 'val ', 'int32', 'int64', 'word']
                if any(pattern in statement_lower for pattern in bitvector_patterns) and 'read' not in statement_lower:
                    filtered.append(theorem)
    
    return filtered

def execute_theorem_setup_code(setup_code: str, theorem_name: str = "") -> bool:
    """Execute setup code for a specific theorem (like smart_proof_validator.py)."""
    if not setup_code or not setup_code.strip():
        print("    No theorem-specific setup code provided")
        return True
        
    try:
        checker = HOLLightChecker(timeout=400)
        if not checker.connect():
            print("    - Cannot connect to server for theorem setup")
            return False
        
        print(f"    Executing theorem setup code for {theorem_name}")
        print("    Setup code content:")
        print("    " + "-" * 40)
        # Show first few lines of setup code for reference
        setup_lines = setup_code.split('\n')
        for line in setup_lines[:5]:
            if line.strip():
                print(f"    {line}")
        if len(setup_lines) > 5:
            remaining_lines = len(setup_lines) - 5
            print(f"    ... ({remaining_lines} more lines)")
        print("    " + "-" * 40)
        
        # Parse and execute setup commands
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
        
        print(f"    Parsed {len(commands)} OCaml commands from setup code")
        
        # Execute setup commands
        failed_commands = []
        for j, command in enumerate(commands, 1):
            print(f"    Executing setup command {j}/{len(commands)}")
            
            # Normalize command to single line
            normalized_command = command.replace('\r\n', ' ').replace('\r', ' ').replace('\n', ' ')
            normalized_command = re.sub(r'\s+', ' ', normalized_command).strip()
            
            if not normalized_command.endswith(';;'):
                normalized_command += ';;'
            
            # Set timeout based on command type
            if 'loadt' in normalized_command or 'needs' in normalized_command:
                timeout = 400
                show_streaming = True
            else:
                timeout = 60
                show_streaming = False
            
            result = checker.send_command(normalized_command, timeout=timeout, show_streaming=show_streaming)
            
            if result.get("success", False):
                print(f"    + Setup command {j} executed successfully")
            else:
                error_msg = result.get('error', 'Unknown error')
                print(f"    - Setup command {j} failed: {error_msg}")
                failed_commands.append((command[:50] + "...", error_msg))
        
        checker.disconnect()
        
        success_rate = (len(commands) - len(failed_commands)) / len(commands) if commands else 1.0
        print(f"    Setup execution completed: {len(commands) - len(failed_commands)}/{len(commands)} successful ({success_rate:.1%})")
        
        if failed_commands:
            print(f"    Failed setup commands:")
            for cmd, error in failed_commands[:3]:  # Show first 3 failures
                print(f"      - {cmd}: {error}")
            if len(failed_commands) > 3:
                print(f"      ... and {len(failed_commands) - 3} more failures")
        
        # Return success if most commands succeeded
        return len(failed_commands) <= len(commands) // 2
        
    except Exception as e:
        print(f"    - Theorem setup execution failed: {e}")
        return False

def process_theorem_batch(theorems: List[Dict[str, Any]], 
                         output_file: Optional[str] = None,
                         max_theorems: Optional[int] = None,
                         start_index: int = 0,
                         filter_classification: Optional[str] = None) -> Dict[str, Any]:
    """Process a batch of theorems and validate their proofs."""
    
    # Apply classification filter if specified
    if filter_classification:
        original_count = len(theorems)
        theorems = filter_theorems_by_classification(theorems, filter_classification)
        print(f"Filtered by classification '{filter_classification}': {len(theorems)} of {original_count} theorems")
        
        if not theorems:
            print(f"No theorems found with classification '{filter_classification}'")
            return {
                "total_processed": 0,
                "successful": 0,
                "failed": 0,
                "skipped": 0,
                "results": [],
                "summary": {
                    "processing_time_seconds": 0,
                    "success_rate": 0,
                    "files_processed": 0,
                    "filter_applied": filter_classification,
                    "theorems_after_filter": 0
                }
            }
    
    results = {
        "total_processed": 0,
        "successful": 0,
        "failed": 0,
        "skipped": 0,
        "results": [],
        "summary": {}
    }
    
    # Limit the number of theorems if specified
    if max_theorems:
        end_index = min(start_index + max_theorems, len(theorems))
        processing_theorems = theorems[start_index:end_index]
        print(f"Processing theorems {start_index+1} to {end_index} (of {len(theorems)} total)")
    else:
        processing_theorems = theorems[start_index:]
        print(f"Processing {len(processing_theorems)} theorems starting from index {start_index+1}")
    
    start_time = time.time()
    
    for i, theorem_data in enumerate(processing_theorems, start_index + 1):
        print(f"\n[{i}/{len(theorems)}] Processing theorem from {theorem_data.get('file', 'unknown')}")
        
        theorem_statement = theorem_data.get('theorem_statement', '')
        description = theorem_data.get('description', '')
        file_name = theorem_data.get('file', 'unknown')
        theorem_name = theorem_data.get('theorem_name', f'theorem_{i}')
        setup_code = theorem_data.get('setup_code', '')
        
        if not theorem_statement:
            print(f"    ! Skipping: Missing theorem statement")
            results["skipped"] += 1
            results["results"].append({
                "index": i,
                "file": file_name,
                "status": "skipped",
                "error": "Missing theorem statement"
            })
            continue
        
        # Truncate long theorem statements for display
        display_statement = theorem_statement[:100] + "..." if len(theorem_statement) > 100 else theorem_statement
        print(f"    Theorem: {theorem_name}")
        print(f"    Statement: {display_statement}")
        if description:
            print(f"    Description: {description[:80]}{'...' if len(description) > 80 else ''}")
        
        # Execute theorem-specific setup code first (like smart_proof_validator.py)
        setup_success = True
        if setup_code and setup_code.strip():
            print(f"    Executing theorem-specific setup code...")
            setup_success = execute_theorem_setup_code(setup_code, theorem_name)
            if not setup_success:
                print(f"    ! Setup code execution had failures, but continuing with proof generation...")
        else:
            print(f"    No theorem-specific setup code found")
        
        # Generate proof using LLM (like hol_demo.py)
        proof_result = prove_theorem_with_llm(theorem_statement, description, "", file_name)
        
        results["total_processed"] += 1
        
        if proof_result["success"]:
            print(f"    + LLM generated proof successfully!")
            print(f"    Tactic: {proof_result.get('tactic_used', 'unknown')}")
            print(f"    Confidence: {proof_result.get('llm_confidence', 0.0):.2f}")
            print(f"    Attempts: {proof_result.get('total_attempts', 1)}")
            
            results["successful"] += 1
            results["results"].append({
                "index": i,
                "file": file_name,
                "theorem_name": theorem_name,
                "status": "success",
                "theorem_statement": theorem_statement,
                "setup_success": setup_success,
                "generated_proof": proof_result.get("proof", ""),
                "tactic_used": proof_result.get("tactic_used", "unknown"),
                "llm_reasoning": proof_result.get("reasoning", ""),
                "llm_confidence": proof_result.get("llm_confidence", 0.0),
                "total_attempts": proof_result.get("total_attempts", 1),
                "time_taken": proof_result.get("time_taken", 0)
            })
        else:
            print(f"    - LLM proof generation failed: {proof_result.get('error', 'Unknown error')}")
            results["failed"] += 1
            results["results"].append({
                "index": i,
                "file": file_name,
                "theorem_name": theorem_name,
                "status": "failed",
                "theorem_statement": theorem_statement,
                "setup_success": setup_success,
                "error": proof_result.get("error", "Unknown error"),
                "total_attempts": proof_result.get("total_attempts", 1)
            })
    
    # Calculate timing and summary
    end_time = time.time()
    processing_time = end_time - start_time
    
    results["summary"] = {
        "processing_time_seconds": processing_time,
        "success_rate": (results["successful"] / results["total_processed"] * 100) if results["total_processed"] > 0 else 0,
        "files_processed": len(set(r.get("file", "") for r in results["results"])),
    }
    
    # Save results if output file specified
    if output_file:
        with open(output_file, 'w') as f:
            json.dump(results, f, indent=2)
        print(f"\n+ Results saved to {output_file}")
    
    return results

def print_summary(results: Dict[str, Any]):
    """Print a summary of the processing results."""
    print("\n" + "=" * 60)
    print("AUTOMATED PROOF BUILDING SUMMARY")
    print("=" * 60)
    print(f"Total processed: {results['total_processed']}")
    print(f"Successful: {results['successful']} ({results['summary']['success_rate']:.1f}%)")
    print(f"Failed: {results['failed']}")
    print(f"Skipped: {results['skipped']}")
    print(f"Files processed: {results['summary']['files_processed']}")
    print(f"Processing time: {results['summary']['processing_time_seconds']:.1f} seconds")
    
    if results['failed'] > 0:
        print(f"\nFailed proofs:")
        for result in results['results']:
            if result['status'] == 'failed':
                print(f"  - {result['file']}: {result['error']}")

def main():
    """Main entry point."""
    parser = argparse.ArgumentParser(description="Automated Proof Builder for s2n-bignum")
    parser.add_argument("input_file", nargs='?', help="JSON file with extracted theorems")
    parser.add_argument("--setup", help="File with OCaml setup commands (one per line)")
    parser.add_argument("--output", "-o", help="Output file for results (JSON format)")
    parser.add_argument("--max-theorems", "-n", type=int, help="Maximum number of theorems to process")
    parser.add_argument("--start-index", "-s", type=int, default=0, help="Starting index (0-based)")
    parser.add_argument("--filter-classification", "-f", help="Filter theorems by classification (e.g., 'bitvector operations')")
    parser.add_argument("--check-server", action="store_true", help="Only check server connection and exit")
    
    args = parser.parse_args()
    
    print("s2n-bignum Automated Proof Builder")
    print("=" * 60)
    
    # Check server connection
    if not check_server():
        sys.exit(1)
    
    if args.check_server:
        print("+ Server check passed")
        sys.exit(0)
    
    # Require input_file if not just checking server
    if not args.input_file:
        parser.error("input_file is required unless using --check-server")
    
    # Load setup commands if provided
    setup_commands = []
    if args.setup:
        try:
            with open(args.setup, 'r') as f:
                setup_commands = [line.strip() for line in f.readlines() if line.strip()]
            print(f"+ Loaded {len(setup_commands)} setup commands from {args.setup}")
        except Exception as e:
            print(f"- Failed to load setup file: {e}")
            sys.exit(1)
    
    # Execute methodical setup (always loads base.ml + additional commands if provided)
    if not setup_ocaml_environment_methodically(setup_commands):
        print("- Methodical setup failed. Aborting.")
        sys.exit(1)
    
    # Load theorems
    try:
        with open(args.input_file, 'r') as f:
            data = json.load(f)
        
        # Handle different JSON structures
        if isinstance(data, list):
            # Direct list format
            theorems = data
        elif isinstance(data, dict) and 'extracted_goals' in data:
            # Nested format from filter_theorems.py
            theorems = data['extracted_goals']
        elif isinstance(data, dict) and 'theorems' in data:
            # Alternative nested format
            theorems = data['theorems']
        else:
            print(f"- Unsupported JSON structure. Keys found: {list(data.keys()) if isinstance(data, dict) else 'Not a dict'}")
            sys.exit(1)
            
        print(f"+ Loaded {len(theorems)} theorems from {args.input_file}")
    except Exception as e:
        print(f"- Failed to load theorems file: {e}")
        sys.exit(1)
    
    # Validate file structure
    if not theorems or not isinstance(theorems, list):
        print("- Invalid file format: expected a list of theorem objects")
        sys.exit(1)
    
    # Check first theorem has expected structure
    sample = theorems[0] if theorems else {}
    expected_keys = ['file', 'theorem_statement']  # Only need statement for LLM proof generation
    missing_keys = [key for key in expected_keys if key not in sample]
    if missing_keys:
        print(f"! Warning: Sample theorem missing keys: {missing_keys}")
        print(f"  Available keys: {list(sample.keys())}")
    
    # Process theorems
    print(f"\nStarting automated proof building...")
    results = process_theorem_batch(
        theorems, 
        args.output, 
        args.max_theorems, 
        args.start_index,
        args.filter_classification
    )
    
    # Print summary
    print_summary(results)
    
    # Exit with appropriate code
    if results["failed"] > 0:
        sys.exit(1)
    else:
        print("\n+ All processed proofs generated successfully!")

if __name__ == "__main__":
    main()

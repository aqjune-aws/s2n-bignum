#!/usr/bin/env python3
"""
HOL Light Theorem Extraction Tool

Extracts theorem proofs from HOL Light source files using JSON metadata
for precise coordinate-based extraction. Processes theorem definitions,
goals, and proofs while preserving source location information.
"""

import json
import os
import time
import re
from typing import Dict, List, Any, Optional, Set, Tuple
from pathlib import Path

class TheoremExtractor:
    """Extracts theorem proofs from HOL Light source files using JSON metadata."""
    
    def __init__(self):
        self.extracted_goals = []
        self.processed_files = []
        self.failed_files = []
        
    def should_include_theorem(self, theorem_info: Dict) -> bool:
        """
        Determine if a theorem should be included based on filtering criteria.
        
        For now, include all theorems and let the separate filter_theorems.py 
        handle the filtering. This ensures we don't miss dependencies.
        """
        return True

    def map_file_path(self, original_path: str) -> Optional[str]:
        """Map absolute paths from JSON to local file paths."""
        # Skip HOL Light library files that don't exist locally
        if '/hol-light/Library/' in original_path:
            return None
            
        # If the original path exists as-is, use it
        if os.path.exists(original_path):
            return original_path
            
        # Map s2n-bignum paths to current directory
        if '/s2n-bignum/' in original_path:
            rel_path = original_path.split('/s2n-bignum/')[-1]
            # Try both current directory and parent directory
            for base_path in ['.', '..']:
                local_path = os.path.join(base_path, rel_path)
                if os.path.exists(local_path):
                    return local_path
        
        # Search common locations by basename
        basename = os.path.basename(original_path)
        search_paths = [
            f'./arm/proofs/{basename}', f'./x86/proofs/{basename}',
            f'./common/{basename}', f'./{basename}',
            f'../arm/proofs/{basename}', f'../x86/proofs/{basename}',
            f'../common/{basename}', f'../{basename}'
        ]
        
        for search_path in search_paths:
            if os.path.exists(search_path):
                return search_path
                
        return None
        
    def load_json_metadata(self, json_file: str) -> List[Dict]:
        """Load theorem metadata from JSON file."""
        try:
            with open(json_file, 'r', encoding='utf-8') as f:
                return json.load(f)
        except Exception as e:
            print(f"Error loading JSON metadata from {json_file}: {e}")
            return []
    
    def read_file_lines(self, filepath: str) -> List[str]:
        """Read file and return lines as list."""
        try:
            with open(filepath, 'r', encoding='utf-8') as f:
                return f.readlines()
        except Exception as e:
            print(f"Error reading file {filepath}: {e}")
            return []
    
    def clean_extracted_text(self, text: str) -> str:
        """Minimal cleaning - just normalize whitespace, preserve original syntax."""
        if not text:
            return text
        
        # Only do minimal cleaning - remove trailing whitespace from lines
        lines = text.split('\n')
        cleaned_lines = []
        
        for line in lines:
            # Remove trailing whitespace but preserve leading indentation
            cleaned_lines.append(line.rstrip())
        
        # Join back and remove excessive newlines at start/end
        result = '\n'.join(cleaned_lines)
        return result.strip()

    def extract_theorem_goal(self, lines: List[str], theorem_info: Dict) -> str:
        """Extract theorem goal using precise line/column information."""
        try:
            start_line = int(theorem_info['goal_linenum_start']) - 1  # Convert to 0-based
            start_col = int(theorem_info['goal_colnum_start']) - 1  # Convert to 0-based
            
            # Find the opening backtick
            opening_line = lines[start_line]
            opening_pos = opening_line.find('`', start_col)
            if opening_pos == -1:
                return ""
            
            # Start collecting the theorem text from the opening backtick
            goal_text = ""
            current_line = start_line
            current_pos = opening_pos
            
            # Search for the matching closing backtick
            while current_line < len(lines):
                line = lines[current_line]
                
                if current_line == start_line:
                    # Start from the opening backtick position
                    search_text = line[current_pos:]
                else:
                    # Search the entire line
                    search_text = line
                
                # Look for backticks in this line
                for i, char in enumerate(search_text):
                    if char == '`':
                        if not goal_text:  # This is the opening backtick
                            goal_text += char
                        else:  # This might be the closing backtick
                            goal_text += char
                            # Clean the extracted text before returning
                            return self.clean_extracted_text(goal_text)
                    else:
                        if goal_text:  # We're inside the theorem statement
                            goal_text += char
                
                # Move to the next line
                current_line += 1
                current_pos = 0
            
            # If we didn't find a closing backtick, return what we have (cleaned)
            return self.clean_extracted_text(goal_text)
            
        except Exception as e:
            print(f"Error extracting goal for {theorem_info['theorem_name']}: {e}")
            return ""
    
    def extract_theorem_proof(self, lines: List[str], theorem_info: Dict) -> str:
        """Extract theorem proof using precise line/column information."""
        try:
            start_line = int(theorem_info['proof_linenum_start']) - 1  # Convert to 0-based
            end_line = int(theorem_info['proof_linenum_end']) - 1
            start_col = int(theorem_info['proof_colnum_start']) - 1  # Convert to 0-based
            end_col = int(theorem_info['proof_colnum_end'])
            
            if start_line == end_line:
                # Single line proof
                proof_text = lines[start_line][start_col:end_col]
            else:
                # Multi-line proof
                proof_parts = []
                # First line
                proof_parts.append(lines[start_line][start_col:])
                # Middle lines
                for i in range(start_line + 1, end_line):
                    proof_parts.append(lines[i])
                # Last line
                proof_parts.append(lines[end_line][:end_col])
                proof_text = ''.join(proof_parts)
            
            # Clean the proof text as well
            return self.clean_extracted_text(proof_text)
        except Exception as e:
            print(f"Error extracting proof for {theorem_info['theorem_name']}: {e}")
            return ""
    
    def extract_complete_theorem(self, lines: List[str], theorem_info: Dict) -> str:
        """Extract complete theorem definition using toplevel line information."""
        try:
            start_line = int(theorem_info['toplevel_theorem_linenum_start']) - 1
            
            # Find the end of the theorem (look for ;; or end of proof)
            proof_end_line = int(theorem_info['proof_linenum_end']) - 1
            
            # Look for ;; after the proof ends
            end_line = proof_end_line
            for i in range(proof_end_line, min(len(lines), proof_end_line + 10)):
                if ';;' in lines[i]:
                    end_line = i
                    break
            
            # Extract the complete theorem
            theorem_lines = lines[start_line:end_line + 1]
            return ''.join(theorem_lines).strip()
        except Exception as e:
            print(f"Error extracting complete theorem for {theorem_info['theorem_name']}: {e}")
            return ""
    
    def extract_constants_from_theorem_statement(self, theorem_statement: str) -> Set[str]:
        """
        Extract constant names referenced in a theorem statement.
        
        For example, from "`prime p_521`", extract {"p_521"}
        """
        constants = set()
        
        # Remove backticks and clean the statement
        clean_statement = theorem_statement.strip('`').strip()
        
        # Look for identifiers that could be constants
        # Pattern matches: word characters, digits, underscores
        # But excludes common keywords and functions
        identifier_pattern = r'\b([a-zA-Z_][a-zA-Z0-9_]*)\b'
        
        # Keywords to exclude (HOL Light functions, common terms)
        excluded_keywords = {
            'prime', 'divides', 'mod', 'rem', 'EXP', 'DIV', 'gcd', 'coprime',
            'abs', 'int', 'num', 'real', 'bool', 'let', 'in', 'if', 'then', 'else',
            'true', 'false', 'and', 'or', 'not', 'forall', 'exists', 'lambda',
            'val', 'word', 'bit', 'bignum_of_wordlist', 'read', 'memory', 'bytes'
        }
        
        for match in re.finditer(identifier_pattern, clean_statement):
            identifier = match.group(1)
            if identifier not in excluded_keywords and not identifier.isdigit():
                constants.add(identifier)
        
        return constants

    def find_definition_lines(self, lines: List[str], constant_name: str) -> Tuple[int, int]:
        """
        Find the start and end lines of a definition for a given constant.
        
        Handles multiple definition patterns:
        1. Simple: let constant_name = ...
        2. Tuple destructuring: let var1,constant_name,var2 = ...
        3. Function definitions: let constant_name param1 param2 = ...
        4. Complex patterns: let constant_name,other = (CONJ_PAIR o prove) ...
        
        Returns (start_line, end_line) or (-1, -1) if not found.
        start_line is 0-indexed.
        """
        for i, line in enumerate(lines):
            line_stripped = line.strip()
            
            # Skip empty lines and comments
            if not line_stripped or line_stripped.startswith('(*'):
                continue
            
            # Must start with 'let'
            if not line_stripped.startswith('let '):
                continue
            
            # Extract the part between 'let' and '='
            eq_pos = line_stripped.find('=')
            if eq_pos == -1:
                continue
            
            let_part = line_stripped[4:eq_pos].strip()  # Skip 'let '
            
            # Check various patterns where the constant might appear
            patterns_to_check = [
                # Simple definition: let constant_name = ...
                rf'^{re.escape(constant_name)}(\s|$)',
                
                # Function definition: let constant_name param1 param2 = ...
                rf'^{re.escape(constant_name)}\s+\w+',
                
                # Tuple destructuring: let var1,constant_name,var2 = ...
                rf'\b{re.escape(constant_name)}\b',
                  
                # Complex tuple with spaces: let var1, constant_name, var2 = ...
                rf',\s*{re.escape(constant_name)}\s*[,=]',
                
                # Start of tuple: let constant_name, var2 = ...
                rf'^{re.escape(constant_name)}\s*,',
            ]
            
            found_match = False
            for pattern in patterns_to_check:
                if re.search(pattern, let_part):
                    found_match = True
                    break
            
            if found_match:
                # Found the start, now find the end (next ;; )
                start_line = i
                for j in range(i, len(lines)):
                    if ';;' in lines[j]:
                        return start_line, j
                # If no ;; found, return just this line
                return start_line, i
        
        return -1, -1

    def extract_basic_setup_code(self, lines: List[str], filename: str) -> str:
        """
        Extract basic setup code using the original algorithm.
        This gets everything before the first theorem definition.
        """
        # Find the first theorem definition
        first_theorem_line = None
        for i, line in enumerate(lines):
            line_stripped = line.strip()
            if '= prove' in line_stripped or '= time prove' in line_stripped:
                first_theorem_line = i
                break
        
        if first_theorem_line is None:
            return ""
        
        # Find the last ;; before the first theorem
        last_setup_line = None
        for i in range(first_theorem_line - 1, -1, -1):
            line_stripped = lines[i].strip()
            if ';;' in line_stripped:
                last_setup_line = i
                break
        
        if last_setup_line is None:
            return ""
        
        # Extract setup lines, skipping comments
        setup_lines = []
        in_multiline_comment = False
        
        for i in range(last_setup_line + 1):
            line = lines[i]
            original_line = line.rstrip()
            line_stripped = line.strip()
            
            # Handle comments
            if '(*' in line_stripped and '*)' in line_stripped:
                if line_stripped.startswith('(*') and line_stripped.endswith('*)'):
                    continue
            elif '(*' in line_stripped and '*)' not in line_stripped:
                if line_stripped.startswith('(*'):
                    in_multiline_comment = True
                    continue
            elif '*)' in line_stripped and in_multiline_comment:
                if line_stripped.endswith('*)'):
                    in_multiline_comment = False
                    continue
            elif in_multiline_comment:
                continue
            
            # Skip empty lines
            if not line_stripped:
                continue
            
            setup_lines.append(original_line)
        
        return '\n'.join(setup_lines)

    def extract_setup_code(self, lines: List[str], filename: str, theorem_info: Dict = None) -> str:
        """
        Improved setup code extraction that includes logical dependencies.
        
        This method:
        1. Extracts the basic setup code (before any theorems)
        2. If theorem_info is provided, identifies constants referenced in the target theorem
        3. Includes definitions of those constants even if they contain 'prove'
        """
        # First, get the basic setup code using the original method
        basic_setup = self.extract_basic_setup_code(lines, filename)
        
        # If no theorem_info provided, just return basic setup
        if theorem_info is None:
            return basic_setup
        
        theorem_name = theorem_info['theorem_name']
        theorem_statement = theorem_info.get('theorem_statement', '')
        
        # Extract constants referenced in the theorem statement
        if not theorem_statement:
            # Try to extract from the theorem goal location
            try:
                theorem_statement = self.extract_theorem_goal(lines, theorem_info)
            except:
                pass
        
        # Also extract constants from the theorem proof (important for dependencies like lemma1, lemma2)
        theorem_proof = ""
        try:
            theorem_proof = self.extract_theorem_proof(lines, theorem_info)
        except:
            pass
        
        # Combine statement and proof for comprehensive dependency analysis
        combined_text = f"{theorem_statement} {theorem_proof}"
        
        if not combined_text.strip():
            return basic_setup
        
        referenced_constants = self.extract_constants_from_theorem_statement(combined_text)
        
        # Find definitions of referenced constants
        additional_definitions = []
        for constant in referenced_constants:
            start_line, end_line = self.find_definition_lines(lines, constant)
            if start_line != -1:
                definition_text = ''.join(lines[start_line:end_line + 1]).strip()
                additional_definitions.append(definition_text)
        
        # Combine basic setup with additional definitions
        setup_parts = [basic_setup] if basic_setup.strip() else []
        setup_parts.extend(additional_definitions)
        
        return '\n'.join(setup_parts)
    
    def clean_machine_code_definition(self, content: str) -> str:
        """Clean machine code definitions by removing comments."""
        # This is a simplified version - you can enhance based on your needs
        lines = content.split('\n')
        cleaned_lines = []
        
        for line in lines:
            # Remove inline comments
            if '(*' in line and '*)' in line:
                # Simple single-line comment removal
                start = line.find('(*')
                end = line.find('*)') + 2
                line = line[:start] + line[end:]
            
            cleaned_lines.append(line)
        
        return '\n'.join(cleaned_lines)
    
    def extract_semantic_annotations(self, theorem_goal: str) -> tuple:
        """Extract semantic tags and math categories from theorem statement."""
        # Simple implementation - can be enhanced based on needs
        semantic_tags = []
        math_categories = []
        
        # Basic pattern matching for common mathematical concepts
        goal_lower = theorem_goal.lower()
        
        if any(word in goal_lower for word in ['modular', 'mod', 'prime']):
            math_categories.append('modular_arithmetic')
        if any(word in goal_lower for word in ['bignum', 'multiplication', 'mul']):
            math_categories.append('arithmetic')
        if any(word in goal_lower for word in ['curve', 'elliptic', 'point']):
            math_categories.append('elliptic_curves')
        if any(word in goal_lower for word in ['inverse', 'inv']):
            math_categories.append('inverse')
        
        return semantic_tags, math_categories
    
    def process_json_file(self, json_filepath: str) -> bool:
        """Process a JSON file and extract theorems from corresponding .ml files."""
        try:
            # Load JSON metadata
            theorems_metadata = self.load_json_metadata(json_filepath)
            if not theorems_metadata:
                return False
            
            # Group theorems by source file, applying path mapping
            files_to_process = {}
            skipped_files = set()
            
            for theorem_info in theorems_metadata:
                original_source_file = theorem_info['filename']
                
                # Apply filtering logic directly during extraction
                if not self.should_include_theorem(theorem_info):
                    continue
                
                mapped_source_file = self.map_file_path(original_source_file)
                
                if mapped_source_file is None:
                    skipped_files.add(original_source_file)
                    continue
                
                if mapped_source_file not in files_to_process:
                    files_to_process[mapped_source_file] = []
                files_to_process[mapped_source_file].append(theorem_info)
            
            total_theorems = 0
            
            # Process each source file
            for source_file, theorems in files_to_process.items():
                
                # Read the source file
                lines = self.read_file_lines(source_file)
                if not lines:
                    continue
                
                filename = os.path.basename(source_file)
                
                # Extract setup code once per file (basic setup, not theorem-specific)
                setup_code = self.extract_setup_code(lines, filename)
                setup_code = self.clean_machine_code_definition(setup_code)
                setup_code = self.clean_extracted_text(setup_code)
                
                # Process each theorem in this file
                for theorem_info in theorems:
                    theorem_name = theorem_info['theorem_name']
                    
                    # Extract theorem components using precise locations
                    theorem_goal = self.extract_theorem_goal(lines, theorem_info)
                    theorem_proof = self.extract_theorem_proof(lines, theorem_info)
                    complete_theorem = self.extract_complete_theorem(lines, theorem_info)
                    
                    if not theorem_goal or not theorem_proof:
                        print(f"Warning: Could not extract goal or proof for {theorem_name}")
                        continue
                    
                    # Format the goal properly
                    if not theorem_goal.startswith('`'):
                        theorem_goal = f"`{theorem_goal}`"
                    
                    # Extract theorem-specific setup code (includes dependencies)
                    theorem_setup_info = theorem_info.copy()
                    theorem_setup_info['theorem_statement'] = theorem_goal
                    theorem_specific_setup = self.extract_setup_code(lines, filename, theorem_setup_info)
                    theorem_specific_setup = self.clean_machine_code_definition(theorem_specific_setup)
                    theorem_specific_setup = self.clean_extracted_text(theorem_specific_setup)
                    
                    # Extract semantic annotations from theorem statement
                    semantic_tags, math_categories = self.extract_semantic_annotations(theorem_goal)
                    
                    goal = {
                        'file': filename,
                        'theorem_name': theorem_name,
                        'description': f"Prove theorem {theorem_name} from {filename}",
                        'setup_code': theorem_specific_setup,
                        'theorem_statement': theorem_goal,
                        'context': f"Theorem {theorem_name} extracted from {filename} using JSON metadata",
                        'complete_proof': complete_theorem,
                        'proof_only': theorem_proof,
                        'semantic_tags': semantic_tags,
                        'math_categories': math_categories,
                        'source_location': {
                            'file': source_file,
                            'original_file': theorem_info['filename'],  # Keep original path for reference
                            'theorem_start_line': theorem_info['toplevel_theorem_linenum_start'],
                            'goal_location': {
                                'start_line': theorem_info['goal_linenum_start'],
                                'start_col': theorem_info['goal_colnum_start'],
                                'end_line': theorem_info['goal_linenum_end'],
                                'end_col': theorem_info['goal_colnum_end']
                            },
                            'proof_location': {
                                'start_line': theorem_info['proof_linenum_start'],
                                'start_col': theorem_info['proof_colnum_start'],
                                'end_line': theorem_info['proof_linenum_end'],
                                'end_col': theorem_info['proof_colnum_end']
                            }
                        }
                    }
                    
                    self.extracted_goals.append(goal)
                    total_theorems += 1
                
                if filename not in self.processed_files:
                    self.processed_files.append(filename)
            
            print(f"✓ Processed {json_filepath}: {total_theorems} theorem(s) extracted from {len(files_to_process)} source file(s)")
            return True
            
        except Exception as e:
            print(f"✗ Error processing {json_filepath}: {e}")
            self.failed_files.append(json_filepath)
            return False
    
    def process_thm_dumps_directory(self, directory: str = "thm_dumps") -> int:
        """Process all JSON files in the thm_dumps directory efficiently."""
        directory_path = Path(directory)
        if not directory_path.exists():
            print(f"Directory {directory} does not exist")
            return 0
        
        json_files = list(directory_path.glob("*.json"))
        if not json_files:
            print(f"No JSON files found in {directory}")
            return 0
        
        print(f"Found {len(json_files)} JSON files in {directory}")
        print("=" * 60)
        
        # Collect all theorem metadata from all JSON files first
        all_theorems = {}  # theorem_name -> theorem_info (deduplicated)
        theorem_sources = set()  # track unique source files
        
        print("Loading theorem metadata...")
        for i, json_file in enumerate(sorted(json_files), 1):
            if i % 50 == 0 or i == len(json_files):
                print(f"  Processed {i}/{len(json_files)} JSON files")
            
            try:
                theorems_metadata = self.load_json_metadata(str(json_file))
                for theorem_info in theorems_metadata:
                    theorem_name = theorem_info['theorem_name']
                    source_file = theorem_info['filename']
                    
                    # Keep all occurrences - let the filter step handle deduplication
                    unique_key = f"{theorem_name}_{source_file}"
                    if unique_key not in all_theorems:
                        all_theorems[unique_key] = theorem_info
                        theorem_sources.add(source_file)
            except Exception as e:
                print(f"Error loading {json_file}: {e}")
                continue
        
        print(f"Found {len(all_theorems)} unique theorems from {len(theorem_sources)} source files")
        
        # Process deduplicated theorems
        if self.process_theorem_batch(list(all_theorems.values())):
            return len(json_files)
        return 0
    
    def process_theorem_batch(self, theorems_metadata: List[Dict]) -> bool:
        """Process a batch of theorem metadata efficiently."""
        # Group theorems by source file, applying path mapping
        files_to_process = {}
        skipped_files = set()
        
        for theorem_info in theorems_metadata:
            original_source_file = theorem_info['filename']
            mapped_source_file = self.map_file_path(original_source_file)
            
            if mapped_source_file is None:
                skipped_files.add(original_source_file)
                continue
            
            if mapped_source_file not in files_to_process:
                files_to_process[mapped_source_file] = []
            files_to_process[mapped_source_file].append(theorem_info)
        
        if skipped_files:
            print(f"Skipped {len(skipped_files)} missing source files")
        
        total_theorems = 0
        print(f"Processing {len(files_to_process)} source files...")
        
        # Process each source file
        for i, (source_file, theorems) in enumerate(files_to_process.items(), 1):
            print(f"  [{i}/{len(files_to_process)}] Processing {os.path.basename(source_file)}: {len(theorems)} theorems")
            
            # Read the source file once
            lines = self.read_file_lines(source_file)
            if not lines:
                continue
            
            filename = os.path.basename(source_file)
            
            # Extract setup code once per file
            setup_code = self.extract_setup_code(lines, filename)
            setup_code = self.clean_machine_code_definition(setup_code)
            setup_code = self.clean_extracted_text(setup_code)
            
            # Process each theorem in this file
            for theorem_info in theorems:
                theorem_name = theorem_info['theorem_name']
                
                # Extract theorem components using precise locations
                theorem_goal = self.extract_theorem_goal(lines, theorem_info)
                theorem_proof = self.extract_theorem_proof(lines, theorem_info)
                complete_theorem = self.extract_complete_theorem(lines, theorem_info)
                
                if not theorem_goal or not theorem_proof:
                    continue
                
                # Format the goal properly
                if not theorem_goal.startswith('`'):
                    theorem_goal = f"`{theorem_goal}`"
                
                # Extract theorem-specific setup code (includes dependencies)
                theorem_setup_info = theorem_info.copy()
                theorem_setup_info['theorem_statement'] = theorem_goal
                theorem_specific_setup = self.extract_setup_code(lines, filename, theorem_setup_info)
                theorem_specific_setup = self.clean_machine_code_definition(theorem_specific_setup)
                theorem_specific_setup = self.clean_extracted_text(theorem_specific_setup)
                
                goal = {
                    'file': filename,
                    'theorem_name': theorem_name,
                    'description': f"Prove theorem {theorem_name} from {filename}",
                    'setup_code': theorem_specific_setup,
                    'theorem_statement': theorem_goal,
                    'context': f"Theorem {theorem_name} extracted from {filename} using JSON metadata",
                    'complete_proof': complete_theorem,
                    'proof_only': theorem_proof,
                    'source_location': {
                        'file': source_file,
                        'original_file': theorem_info['filename'],
                        'theorem_start_line': theorem_info['toplevel_theorem_linenum_start'],
                        'goal_location': {
                            'start_line': theorem_info['goal_linenum_start'],
                            'start_col': theorem_info['goal_colnum_start'],
                            'end_line': theorem_info['goal_linenum_end'],
                            'end_col': theorem_info['goal_colnum_end']
                        },
                        'proof_location': {
                            'start_line': theorem_info['proof_linenum_start'],
                            'start_col': theorem_info['proof_colnum_start'],
                            'end_line': theorem_info['proof_linenum_end'],
                            'end_col': theorem_info['proof_colnum_end']
                        }
                    }
                }
                
                self.extracted_goals.append(goal)
                total_theorems += 1
            
            if filename not in self.processed_files:
                self.processed_files.append(filename)
        
        print(f"✓ Extracted {total_theorems} unique theorems from {len(files_to_process)} source files")
        return True
    
    def save_results(self, output_file: str = "json_based_proofs_extracted.json"):
        """Save extracted goals to JSON file."""
        timestamp = time.strftime("%Y%m%d_%H%M%S")
        
        results = {
            "extraction_info": {
                "timestamp": timestamp,
                "extraction_method": "JSON metadata based",
                "total_files_processed": len(self.processed_files),
                "successful_extractions": len(self.extracted_goals),
                "failed_files": len(self.failed_files),
                "files_processed": self.processed_files,
                "files_failed": self.failed_files
            },
            "extracted_goals": self.extracted_goals
        }
        
        with open(output_file, 'w', encoding='utf-8') as f:
            json.dump(results, f, indent=2, ensure_ascii=False)
        
        print(f"\n" + "=" * 60)
        print(f"EXTRACTION COMPLETE")
        print(f"Results saved to: {output_file}")
        print(f"Total goals extracted: {len(self.extracted_goals)}")
        print(f"Files processed successfully: {len(self.processed_files)}")
        print(f"Files failed: {len(self.failed_files)}")
        
        if self.failed_files:
            print(f"Failed files: {', '.join(self.failed_files)}")
        
        # Show summary by file
        file_summary = {}
        for goal in self.extracted_goals:
            filename = goal['file']
            if filename not in file_summary:
                file_summary[filename] = []
            file_summary[filename].append(goal['theorem_name'])
        
        print(f"\nSUMMARY BY FILE:")
        for filename, theorems in sorted(file_summary.items()):
            print(f"  {filename}: {len(theorems)} theorem(s) - {', '.join(theorems[:5])}")
            if len(theorems) > 5:
                print(f"    ... and {len(theorems) - 5} more")

def main():
    """Main entry point to extract using JSON metadata."""
    import argparse
    
    parser = argparse.ArgumentParser(description="Extract Proof Goals using JSON Metadata")
    parser.add_argument("--output", default="json_based_proofs_extracted.json",
                       help="Output JSON file (default: json_based_proofs_extracted.json)")
    parser.add_argument("--directory", default="thm_dumps",
                       help="Directory containing JSON metadata files (default: thm_dumps)")
    parser.add_argument("--json-file", 
                       help="Process a specific JSON file instead of entire directory")
    
    args = parser.parse_args()
    
    print("JSON-BASED PROOF EXTRACTION SCRIPT")
    print("=" * 60)
    print("Extracting proof goals using precise JSON metadata")
    print("Features:")
    print("- Uses precise line/column information from JSON metadata")
    print("- Extracts exact theorem goals and proofs")
    print("- Preserves source location information")
    print("=" * 60)
    
    extractor = TheoremExtractor()
    
    if args.json_file:
        # Process a specific JSON file
        successful_files = 1 if extractor.process_json_file(args.json_file) else 0
    else:
        # Process all JSON files in the directory
        successful_files = extractor.process_thm_dumps_directory(args.directory)
    
    if successful_files > 0:
        extractor.save_results(args.output)
        
        print(f"\nTo validate the extracted proofs, run:")
        print(f"python3 proof_validator.py {args.output}")
        
        return 0
    else:
        print("\nNo files were successfully processed")
        return 1

if __name__ == "__main__":
    exit(main())

#!/usr/bin/env python3

import json
import os
from pathlib import Path

def classify_theorem(theorem_name, theorem_statement):
    """
    Classify theorems into different categories based on their name and statement.
    """
    # Convert to lowercase for easier matching
    name_lower = theorem_name.lower()
    statement_lower = theorem_statement.lower()
    
    # Check for functional correctness of assembly programs
    if name_lower.endswith('_correct'):
        return 'functional correctness of assembly programs'
    
    # Check for register-related theorems
    if 'read' in statement_lower:
        return 'register_related'
    
    # Check for bitvector operations
    # Include 'word_' patterns and also 'val ', 'int32', 'int64', 'word' patterns
    bitvector_patterns = ['word_', 'val ', 'int32', 'int64', 'word']
    if any(pattern in statement_lower for pattern in bitvector_patterns) and 'read' not in statement_lower:
        return 'bitvector operations'
    
    # Default classification
    return 'other'

def filter_theorems_by_proofs_folders(specific_include_files=None):
    """
    Filter extracted_theorems.json to only keep theorems from .ml files 
    that are present in arm/proofs and x86/proofs directories.
    
    Args:
        specific_include_files: Set of specific .ml files to include (overrides default filtering)
    """
    
    # Get list of .ml files from arm/proofs and x86/proofs directories
    proof_files = set()
    
    # Files to exclude from filtering
    excluded_files = {'neon_helper.ml'}
    
    # Default specific files to include (overrides other filtering criteria)
    # Set this to extract from specific individual files
    if specific_include_files is None:
        specific_include_files = {
            # 'bignum_inv_p521.ml',  # Uncomment to include this specific file
            # 'bignum_add.ml',       # Uncomment to include this specific file
            # Add more files here as needed
        }
    
    # Check arm/proofs directory
    arm_proofs_dir = Path("arm/proofs")
    if arm_proofs_dir.exists():
        arm_files_with_underscore = []
        for ml_file in arm_proofs_dir.glob("*.ml"):
            if '_' in ml_file.name and ml_file.name not in excluded_files:
                proof_files.add(ml_file.name)
                arm_files_with_underscore.append(ml_file.name)
        print(f"Found {len([f for f in arm_proofs_dir.glob('*.ml')])} .ml files in arm/proofs")
        print(f"Kept {len(arm_files_with_underscore)} files with underscore in name (excluding {excluded_files})")
    else:
        print(f"Warning: {arm_proofs_dir} directory not found")
    
    # Check x86/proofs directory
    x86_proofs_dir = Path("x86/proofs")
    if x86_proofs_dir.exists():
        x86_files = list(x86_proofs_dir.glob("*.ml"))
        x86_files_with_underscore = []
        for ml_file in x86_files:
            if '_' in ml_file.name and ml_file.name not in excluded_files:
                proof_files.add(ml_file.name)
                x86_files_with_underscore.append(ml_file.name)
        print(f"Found {len(x86_files)} .ml files in x86/proofs")
        print(f"Kept {len(x86_files_with_underscore)} files with underscore in name (excluding {excluded_files})")
    else:
        print(f"Warning: {x86_proofs_dir} directory not found")
    
    # Apply specific file filtering if configured
    if specific_include_files:
        print(f"SPECIFIC FILE MODE: Only including files: {specific_include_files}")
        proof_files = proof_files.intersection(specific_include_files)
        print(f"Files after specific filtering: {len(proof_files)} files")
        if proof_files:
            print(f"Included files: {sorted(list(proof_files))}")
        else:
            print("WARNING: No files match the specific include criteria!")
    else:
        print(f"Total unique .ml files found in proofs directories: {len(proof_files)}")
        print(f"Sample files: {sorted(list(proof_files))[:10]}...")  # Show first 10 files as sample
    
    # Load the extracted theorems JSON
    json_file = Path("my_theorems.json")
    if not json_file.exists():
        print(f"Error: {json_file} not found")
        return
    
    with open(json_file, 'r') as f:
        data = json.load(f)
    
    # Get the list of theorems from the JSON structure
    theorems = data.get('extracted_goals', [])
    print(f"Original JSON contains {len(theorems)} theorems")
    
    # Filter theorems to only keep those from files that exist in arm/proofs or x86/proofs
    # and retain only specified fields with classification
    filtered_theorems = []
    excluded_theorems = []
    
    # Fields to retain
    required_fields = ['file', 'theorem_name', 'description', 'setup_code', 'theorem_statement', 'complete_proof', 'proof_only']
    
    for theorem in theorems:
        # Get the filename from the theorem (should be in the 'file' field)
        if 'file' in theorem:
            theorem_file = theorem['file']
            
            # Check if this file exists in proof directories
            if theorem_file in proof_files:
                # Check if this is a _CORRECT theorem that uses EQUIV_ tactics
                theorem_name = theorem.get('theorem_name', '')
                complete_proof = theorem.get('complete_proof', '')
                proof_only = theorem.get('proof_only', '')
                
                # Check if theorem name ends with _CORRECT and proof contains EQUIV_ tactics
                if theorem_name.lower().endswith('_correct') and ('EQUIV_' in complete_proof or 'EQUIV_' in proof_only):
                    # Exclude this theorem
                    excluded_theorem = {
                        'file': theorem_file,
                        'theorem_name': theorem_name,
                        'description': theorem.get('description', ''),
                        'exclusion_reason': '_CORRECT theorem uses EQUIV_ tactics in proof'
                    }
                    excluded_theorems.append(excluded_theorem)
                    print(f"Excluding {theorem_name} from {theorem_file} (CORRECT theorem with EQUIV_ tactics)")
                else:
                    # Create filtered theorem with only required fields
                    filtered_theorem = {}
                    
                    # Copy required fields if they exist
                    for field in required_fields:
                        if field in theorem:
                            filtered_theorem[field] = theorem[field]
                        else:
                            filtered_theorem[field] = ""  # Set empty string for missing fields
                    
                    # Add classification based on theorem name and statement content
                    theorem_statement = theorem.get('theorem_statement', '')
                    filtered_theorem['classification'] = classify_theorem(theorem_name, theorem_statement)
                    
                    filtered_theorems.append(filtered_theorem)
            else:
                # Track excluded theorem
                excluded_theorem = {
                    'file': theorem_file,
                    'theorem_name': theorem.get('theorem_name', ''),
                    'description': theorem.get('description', ''),
                    'exclusion_reason': 'Source file not found in arm/proofs or x86/proofs directories'
                }
                excluded_theorems.append(excluded_theorem)
                print(f"Excluding theorem from {theorem['file']} (not found in arm/proofs or x86/proofs)")
        else:
            # Track theorems missing file field
            excluded_theorem = {
                'file': 'MISSING_FILE_FIELD',
                'theorem_name': theorem.get('theorem_name', 'Unknown'),
                'description': theorem.get('description', ''),
                'exclusion_reason': 'Theorem missing file field'
            }
            excluded_theorems.append(excluded_theorem)
            print(f"Warning: Theorem missing 'file' field: {theorem.get('theorem_name', 'Unknown')}")
    
    print(f"Filtered JSON contains {len(filtered_theorems)} theorems")
    
    # Print classification distribution
    classification_counts = {}
    for theorem in filtered_theorems:
        classification = theorem.get('classification', 'unknown')
        classification_counts[classification] = classification_counts.get(classification, 0) + 1
    
    print(f"\nClassification distribution:")
    for classification, count in sorted(classification_counts.items()):
        print(f"  {classification}: {count} theorems")
    
    # Save the filtered results with the same structure as the original
    filtered_data = {
        "extraction_info": data.get("extraction_info", {}),
        "extracted_goals": filtered_theorems
    }
    
    output_file = Path("benchmark/extracted_theorems_proofs_only.json")
    with open(output_file, 'w') as f:
        json.dump(filtered_data, f, indent=2)
    
    print(f"Filtered theorems saved to {output_file}")
    
    # Save the excluded theorems
    excluded_data = {
        "exclusion_info": {
            "total_excluded": len(excluded_theorems),
            "exclusion_summary": "Theorems excluded during filtering process"
        },
        "excluded_theorems": excluded_theorems
    }
    
    excluded_output_file = Path("benchmark/excluded_theorems.json")
    with open(excluded_output_file, 'w') as f:
        json.dump(excluded_data, f, indent=2)
    
    print(f"Excluded theorems saved to {excluded_output_file}")
    print(f"Total excluded theorems: {len(excluded_theorems)}")
    
    # Print summary of excluded theorems by source
    excluded_by_source = {}
    for theorem in excluded_theorems:
        source_file = theorem.get('file', 'UNKNOWN')
        if source_file not in excluded_by_source:
            excluded_by_source[source_file] = []
        excluded_by_source[source_file].append(theorem)
    
    if excluded_theorems:
        print(f"\nExcluded theorems by source:")
        for source_file in sorted(excluded_by_source.keys()):
            count = len(excluded_by_source[source_file])
            print(f"  {source_file}: {count} theorems")
            # Show exclusion reasons for this source
            reasons = set(t.get('exclusion_reason', 'Unknown') for t in excluded_by_source[source_file])
            for reason in sorted(reasons):
                reason_count = sum(1 for t in excluded_by_source[source_file] if t.get('exclusion_reason') == reason)
                print(f"    - {reason}: {reason_count}")
    
    # Print summary of what was kept
    kept_files = set()
    for theorem in filtered_theorems:
        if 'file' in theorem:
            kept_files.add(theorem['file'])
    
    print(f"\nKept theorems from {len(kept_files)} files:")
    for file in sorted(kept_files):
        count = sum(1 for t in filtered_theorems if t.get('file') == file)
        print(f"  {file}: {count} theorems")

def main():
    """Main function with command line argument support."""
    import argparse
    
    parser = argparse.ArgumentParser(
        description="Filter extracted theorems by proof files",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
Examples:
  # Extract from all proof files (default behavior)
  python3 filter_theorems.py
  
  # Extract only from specific files
  python3 filter_theorems.py --include bignum_inv_p521.ml bignum_add.ml
  
  # Extract from a single specific file
  python3 filter_theorems.py --include bignum_inv_p521.ml
        """
    )
    
    parser.add_argument(
        "--include", 
        nargs='+', 
        help="Specific .ml files to include (overrides default filtering)"
    )
    
    args = parser.parse_args()
    
    # Pass specific files to the filtering function
    if args.include:
        specific_include_files = set(args.include)
        print(f"Command line override: Including only {specific_include_files}")
        filter_theorems_by_proofs_folders(specific_include_files)
    else:
        filter_theorems_by_proofs_folders()

if __name__ == "__main__":
    main()

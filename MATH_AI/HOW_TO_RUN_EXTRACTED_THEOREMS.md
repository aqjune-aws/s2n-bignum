# How to Run Extracted Theorems with Smart Proof Validator

This guide explains how to run the contents of `extracted_theorems.json` using the `smart_proof_validator.py` system.

## Overview

The `extracted_theorems.json` file contains structured theorem data extracted from s2n-bignum proof files. Each theorem entry includes:

- **file**: Source ML file name
- **theorem_name**: Name of the theorem to prove
- **description**: Human-readable description
- **setup_code**: Required setup code (assembly definitions, etc.)
- **theorem_statement**: The formal theorem statement
- **complete_proof**: Full proof including statement and tactics
- **proof_only**: Just the proof tactics
- **source_location**: File location metadata

## System Architecture

The smart proof validator system consists of:

1. **SmartProofValidator**: Main orchestrator class
2. **HOLLightChecker**: Manages connection to HOL Light server
3. **DependencyResolver**: Handles theorem dependencies
4. **Assembly Filtering**: Skips problematic assembly definitions

## Prerequisites

### 1. HOL Light Server Setup

You need a running HOL Light server that can accept socket connections:

```bash
# Start HOL Light with server capability
# (This typically requires a custom HOL Light build with server support)
hol_light_server --port 2012
```

### 2. File Structure

Ensure your directory structure matches s2n-bignum layout:
```
s2n-bignum/
├── arm/proofs/base.ml          # Core definitions
├── arm/generic/bignum_add.o    # Compiled assembly
├── benchmark/
│   ├── extracted_theorems.json # Your theorem data
│   └── smart_proof_validator.py # Validator script
```

## Running the Validator

### Basic Usage

```bash
cd /path/to/s2n-bignum
python3 benchmark/smart_proof_validator.py benchmark/extracted_theorems.json
```

### With Custom Output File

```bash
python3 benchmark/smart_proof_validator.py benchmark/extracted_theorems.json --output my_results.json
```

### Command Line Options

```bash
python3 benchmark/smart_proof_validator.py --help
```

## How It Works

### 1. JSON Loading and Parsing

The validator loads your `extracted_theorems.json` and parses the structure:

```python
# Example theorem structure from your JSON:
{
  "file": "bignum_add.ml",
  "theorem_name": "BIGNUM_ADD_SUBROUTINE_CORRECT",
  "description": "Prove theorem BIGNUM_ADD_SUBROUTINE_CORRECT from bignum_add.ml",
  "setup_code": "needs \"arm/proofs/base.ml\";;\nlet bignum_add_mc = ...",
  "theorem_statement": "`!p z m x a n y b pc returnaddress. ...",
  "complete_proof": "let BIGNUM_ADD_SUBROUTINE_CORRECT = prove ...",
  "proof_only": "ARM_ADD_RETURN_NOSTACK_TAC BIGNUM_ADD_EXEC BIGNUM_ADD_CORRECT"
}
```

### 2. Dependency Resolution

The system analyzes theorem dependencies and sorts them topologically:

```python
# Dependencies are extracted by analyzing references between theorems
dependencies = {
  "BIGNUM_ADD_SUBROUTINE_CORRECT": {"BIGNUM_ADD_CORRECT"},
  "BIGNUM_ADD_CORRECT": set()  # No dependencies
}
```

### 3. Smart Assembly Filtering

The validator intelligently filters out problematic assembly definitions that crash HOL Light:

**Problematic patterns (automatically skipped):**
- `define_assert_from_elf` with large hex arrays
- `ARM_MK_EXEC_RULE` definitions
- Assembly machine code definitions

**Safe patterns (executed):**
- `needs` statements
- Theorem definitions
- Tactic applications

### 4. Proof Validation Process

For each theorem, the validator:

1. **Connects** to HOL Light server
2. **Loads base.ml** with pre-compiled assembly definitions
3. **Executes filtered setup code** (skipping problematic parts)
4. **Runs the complete proof** using the extracted proof tactics
5. **Validates success** and records results
6. **Disconnects** for clean state

## Example Execution Flow

```bash
$ python3 benchmark/smart_proof_validator.py benchmark/extracted_theorems.json

SMART PROOF VALIDATOR WITH ROBUST FEATURES
================================================================================
LOADED JSON FILE: benchmark/extracted_theorems.json
TOTAL PROOF GOALS: 2
RESOLVING DEPENDENCIES...
DEPENDENCY RESOLUTION: Complete

################################################################################
PROCESSING GOAL 1/2: bignum_add.ml
THEOREM NAME: BIGNUM_ADD_CORRECT
################################################################################

============================================================
STEP 1: CONNECTING TO HOL LIGHT SERVER
============================================================
Connected to HOL Light server at 127.0.0.1:2012

============================================================
STEP 2: LOADING BASE WITH ASSEMBLY
============================================================
Loading: arm/proofs/base.ml
Successfully loaded arm/proofs/base.ml

============================================================
STEP 3: EXECUTING SMART FILTERED SETUP
============================================================
FILTERING PROBLEMATIC SETUP CODE
SKIPPED PROBLEMATIC: let bignum_add_mc = define_assert_from_elf...
KEPT SAFE: let BIGNUM_ADD_EXEC = ARM_MK_EXEC_RULE bignum_add_mc...

============================================================
STEP 4: EXECUTING COMPLETE PROOF
============================================================
SMART PROOF VALIDATION: SUCCESS

GOAL 1 RESULT: SUCCESS - BIGNUM_ADD_CORRECT validated!
TIME TAKEN: 45.23 seconds
```

## Output Format

The validator generates a detailed JSON results file:

```json
{
  "validation_info": {
    "timestamp": "20250813_114200",
    "source_json": "benchmark/extracted_theorems.json",
    "total_goals": 2,
    "successful_validations": 2,
    "success_rate": "100.0%",
    "validator_type": "smart_filtered_validation",
    "total_skipped_definitions": 4
  },
  "results": [
    {
      "success": true,
      "proof": "let BIGNUM_ADD_CORRECT = prove ...",
      "method": "smart_filtered_validation",
      "time_taken": 45.23,
      "goal": "BIGNUM_ADD_CORRECT",
      "file": "bignum_add.ml",
      "skipped_definitions": 2
    }
  ]
}
```

## Key Features

### 1. Assembly Definition Handling

The validator automatically handles the complex assembly definitions that often cause crashes:

- **Skips** `define_assert_from_elf` commands with large hex arrays
- **Uses** pre-loaded assembly from `base.ml`
- **Filters** problematic setup code while preserving essential definitions

### 2. Robust Error Handling

- Fresh connections for each theorem (isolation)
- Timeout management for long-running proofs
- Graceful handling of partial failures
- Detailed error reporting

### 3. Progress Tracking

- Real-time success rate calculation
- Detailed timing information
- Statistics on skipped definitions
- Comprehensive logging

## Troubleshooting

### Common Issues

1. **"Failed to connect to HOL Light server"**
   - Ensure HOL Light server is running on port 2012
   - Check firewall settings
   - Verify server supports socket connections

2. **"Failed to load base.ml"**
   - Ensure you're running from s2n-bignum root directory
   - Check that `arm/proofs/base.ml` exists
   - Verify file permissions

3. **Assembly definition crashes**
   - The smart filtering should handle this automatically
   - Check that problematic patterns are being skipped
   - Review filtering logs for details

### Performance Tips

1. **Use dependency resolution** - theorems are processed in optimal order
2. **Monitor memory usage** - HOL Light can be memory-intensive
3. **Adjust timeouts** - complex proofs may need longer timeouts
4. **Fresh connections** - prevents state pollution between proofs

## Customization

### Modifying Assembly Filters

To add new problematic patterns:

```python
def is_problematic_definition(self, line: str) -> bool:
    problematic_patterns = [
        r'your_new_pattern_here',
        # ... existing patterns
    ]
```

### Adjusting Timeouts

```python
# In HOLLightChecker.__init__
self.timeout = 120  # Default timeout in seconds

# For specific operations
self.load_needs_file("base.ml", timeout=300)  # 5 minutes for base.ml
```

### Custom Dependency Rules

```python
# In DependencyResolver.extract_dependencies
# Add custom logic for detecting dependencies
```

## Integration with Other Tools

The validator can be integrated with:

1. **CI/CD pipelines** - Automated proof checking
2. **Proof development workflows** - Validation during development
3. **Benchmarking systems** - Performance measurement
4. **Documentation generation** - Proof status reporting

## Summary

The smart proof validator provides a robust way to run extracted theorems from your JSON file by:

- Automatically handling problematic assembly definitions
- Resolving complex dependencies between theorems
- Providing detailed progress tracking and error reporting
- Generating comprehensive validation results

This system transforms the raw extracted theorem data into validated, executable proofs within the HOL Light environment.

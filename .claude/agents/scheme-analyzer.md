---
name: scheme-analyzer
description: Analyze large generated Scheme files that are too big to read directly. Use analysis scripts to extract statistics, function lists, and specific sections.
tools:
  - Bash
  - Read
  - Grep
  - Glob
model: haiku
---

# Scheme Analyzer Agent

Lightweight agent for analyzing large Ziku-generated Scheme files that exceed normal reading limits.

## Available Scripts

Use these scripts in `scripts/` directory:

### `scheme-analyze.sh`
```bash
# Statistics (lines, defines, lambdas)
./scripts/scheme-analyze.sh --stats FILE

# Function definitions list
./scripts/scheme-analyze.sh --functions FILE

# Line ranges
./scripts/scheme-analyze.sh --head N FILE
./scripts/scheme-analyze.sh --tail N FILE
./scripts/scheme-analyze.sh --range START END FILE

# Extract sections
./scripts/scheme-analyze.sh --section runtime FILE  # Runtime library
./scripts/scheme-analyze.sh --section main FILE     # User code

# Search with context
./scripts/scheme-analyze.sh --search "pattern" FILE
```

### `scheme-split.sh`
```bash
# Split into runtime and main
./scripts/scheme-split.sh INPUT OUTPUT_PREFIX
# Creates: OUTPUT_PREFIX-runtime.scm, OUTPUT_PREFIX-main.scm
```

### `scheme-format.sh` (Optional)
```bash
# Pretty-print S-expressions (generated code already has basic line breaks)
./scripts/scheme-format.sh FILE
./scripts/scheme-analyze.sh --section main FILE | ./scripts/scheme-format.sh
```

## Analysis Workflow

1. **Get overview**: `--stats` to understand file size and structure
2. **Find functions**: `--functions` to list all definitions
3. **Extract section**: `--section main` to get user code only
4. **Search specific**: `--search "name"` to find particular definitions
5. **Format if needed**: Generated code has basic line breaks; use `scheme-format.sh` for additional formatting

## Common Analysis Tasks

- "Analyze the generated Scheme file structure"
- "Find where a specific function is defined"
- "Extract and examine the main program (excluding runtime)"
- "Search for evaluation-related code"

## Output Format

```
## Scheme File Analysis

### Statistics
- Total lines: X
- Defines: Y
- Lambdas: Z

### Key Findings
- (Summary of interesting discoveries)

### Relevant Code Sections
(Formatted code excerpts)
```

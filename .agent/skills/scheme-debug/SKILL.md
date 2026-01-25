---
description: Debug large Ziku-generated Scheme files. Use when user asks to "analyze Scheme output", "debug generated code", "inspect large Scheme file", or when Scheme files are too large to read directly. (project)
---

# Scheme Debug Skill

Debug and analyze large Ziku-generated Scheme files that exceed normal reading limits.

## Quick Start

```bash
# Generate Scheme file from multiple Ziku sources
./scripts/concat-run.sh --scheme file1.ziku file2.ziku > output.scm

# Get statistics
./scripts/scheme-analyze.sh --stats output.scm

# List all function definitions
./scripts/scheme-analyze.sh --functions output.scm

# Extract user code only (exclude runtime)
./scripts/scheme-analyze.sh --section main output.scm
```

## Available Scripts

### `scheme-analyze.sh` - File Analysis

```bash
# Statistics (lines, chars, defines, lambdas)
./scripts/scheme-analyze.sh --stats FILE

# Function definitions list (max 100)
./scripts/scheme-analyze.sh --functions FILE

# Line ranges
./scripts/scheme-analyze.sh --head N FILE        # First N lines
./scripts/scheme-analyze.sh --tail N FILE        # Last N lines
./scripts/scheme-analyze.sh --range START END FILE  # Lines START to END

# Extract sections
./scripts/scheme-analyze.sh --section runtime FILE  # Runtime library
./scripts/scheme-analyze.sh --section main FILE     # User code only

# Search with context
./scripts/scheme-analyze.sh --search "pattern" FILE
```

### `scheme-split.sh` - File Splitting

```bash
# Split into runtime and main files
./scripts/scheme-split.sh input.scm output_prefix
# Creates: output_prefix-runtime.scm, output_prefix-main.scm
```

### `scheme-format.sh` - Pretty Printing (Optional)

**Note:** Generated Scheme code now includes line breaks for basic readability.
Use `scheme-format.sh` only when deeper indentation is needed.

```bash
# Format entire file (uses Chez Scheme's pretty-print)
./scripts/scheme-format.sh file.scm

# Pipe with other tools
./scripts/scheme-analyze.sh --section main file.scm | ./scripts/scheme-format.sh

# Format search results
./scripts/scheme-analyze.sh --search "define my-func" file.scm | ./scripts/scheme-format.sh
```

## Debugging Workflow

### 1. Overview First
```bash
./scripts/scheme-analyze.sh --stats .mal_tmp.scm
```
Understand file size and structure before diving in.

### 2. Find Functions
```bash
./scripts/scheme-analyze.sh --functions .mal_tmp.scm
```
Get a list of all defined functions with line numbers.

### 3. Extract User Code
```bash
./scripts/scheme-analyze.sh --section main .mal_tmp.scm > main.scm
```
Exclude runtime library to focus on generated user code.

### 4. Search Specific Code
```bash
./scripts/scheme-analyze.sh --search "ziku-eval" .mal_tmp.scm
```
Find specific function definitions or patterns.

### 5. Format for Readability (Optional)
```bash
./scripts/scheme-analyze.sh --section main .mal_tmp.scm | ./scripts/scheme-format.sh | head -100
```
Generated code now has basic line breaks. Use `scheme-format.sh` for additional pretty-printing if needed.

## Common Scenarios

### Debugging Evaluation Issues
```bash
# Find eval-related code
./scripts/scheme-analyze.sh --search "eval" .mal_tmp.scm

# Extract and format
./scripts/scheme-analyze.sh --search "define.*eval" .mal_tmp.scm | ./scripts/scheme-format.sh
```

### Analyzing Runtime vs User Code
```bash
# Split the file
./scripts/scheme-split.sh .mal_tmp.scm /tmp/split

# Analyze each part separately
./scripts/scheme-analyze.sh --stats /tmp/split-runtime.scm
./scripts/scheme-analyze.sh --stats /tmp/split-main.scm
```

### Finding Definition Locations
```bash
# Where is a specific function defined?
./scripts/scheme-analyze.sh --functions .mal_tmp.scm | grep "my-func"

# Get context around that line
./scripts/scheme-analyze.sh --range 100 120 .mal_tmp.scm
```

## Best Practices

1. **Always check stats first** - Know file size before attempting to read
2. **Use section extraction** - Runtime is often large; extract main for user code
3. **Format if needed** - Generated code has basic line breaks; use `scheme-format.sh` for deeper indentation
4. **Use scheme-analyzer agent** - For complex analysis, invoke the scheme-analyzer subagent

## Integration with Agents

Use the `scheme-analyzer` agent for automated analysis:
```
"Analyze the generated Scheme file at .mal_tmp.scm"
```

The agent will use these scripts to provide structured analysis.

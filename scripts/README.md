# Scripts Directory

Utility scripts for Ziku development, testing, and debugging.

## Execution Tools

### `concat-run.sh`
Concatenate multiple Ziku files and run or compile them.

```bash
# Run compiled Scheme
./scripts/concat-run.sh file1.ziku file2.ziku

# Output Scheme code only
./scripts/concat-run.sh --scheme file1.ziku file2.ziku
```

### `run-scheme.sh`
Compile and run a single Ziku file via Scheme.

```bash
./scripts/run-scheme.sh examples/factorial.ziku
```

### `run-docker.sh`
Start Docker container for Ziku development.

```bash
./scripts/run-docker.sh
```

## Analysis / Debug Tools

### `scheme-analyze.sh`
Analyze large generated Scheme files without loading them entirely.

```bash
# File statistics
./scripts/scheme-analyze.sh --stats .mal_tmp.scm

# List function definitions
./scripts/scheme-analyze.sh --functions .mal_tmp.scm

# Extract sections
./scripts/scheme-analyze.sh --section main .mal_tmp.scm   # User code
./scripts/scheme-analyze.sh --section runtime .mal_tmp.scm # Runtime

# Search with context
./scripts/scheme-analyze.sh --search "pattern" .mal_tmp.scm

# Line ranges
./scripts/scheme-analyze.sh --head 50 .mal_tmp.scm
./scripts/scheme-analyze.sh --tail 50 .mal_tmp.scm
./scripts/scheme-analyze.sh --range 100 200 .mal_tmp.scm
```

### `scheme-split.sh`
Split generated Scheme code into runtime and main parts.

```bash
./scripts/scheme-split.sh .mal_tmp.scm /tmp/output
# Creates: /tmp/output-runtime.scm, /tmp/output-main.scm
```

### `scheme-format.sh` (Optional)
Pretty-print S-expressions using Chez Scheme.
Generated code now has basic line breaks; use this for additional formatting.

```bash
# Format file
./scripts/scheme-format.sh .mal_tmp.scm

# Pipe from other tools
./scripts/scheme-analyze.sh --section main .mal_tmp.scm | ./scripts/scheme-format.sh
```

### Testing via mise (Docker)

Test Ziku expressions through compilation phases using `mise run docker:run`:

```bash
mise run docker:run parse 'let x = 1 in x'
mise run docker:run infer 'let x = 1 in x'
mise run docker:run eval 'let x = 1 in x'
mise run docker:run translate 'let x = 1 in x'
mise run docker:run scheme 'let x = 1 in x'
```

## Test Infrastructure

### `aggregate-test-results.sh`
Aggregate test results from multiple test runs.

### `golden-test-viewer.sh`
View and compare golden test results.

### `compare-big-step.py`
Compare big-step and small-step evaluation for consistency.

```bash
python3 scripts/compare-big-step.py
```

## Typical Debugging Workflow

1. Generate Scheme code:
   ```bash
   ./scripts/concat-run.sh --scheme examples/mal/core.ziku examples/mal/step5.ziku > output.scm
   ```

2. Analyze structure:
   ```bash
   ./scripts/scheme-analyze.sh --stats output.scm
   ./scripts/scheme-analyze.sh --functions output.scm
   ```

3. Extract and examine user code (generated code now has basic line breaks):
   ```bash
   ./scripts/scheme-analyze.sh --section main output.scm | head -100
   # Or with additional formatting:
   ./scripts/scheme-analyze.sh --section main output.scm | ./scripts/scheme-format.sh | head -100
   ```

4. Search for specific functions:
   ```bash
   ./scripts/scheme-analyze.sh --search "my-function" output.scm
   ```

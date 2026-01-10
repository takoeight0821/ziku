---
description: Test and debug Ziku expressions through compilation phases. Use when user asks to "test an expression", "check type inference", "debug evaluation", "see IR translation", or "generate Scheme code". (project)
---

# Ziku Test Skill

Test and debug Ziku expressions through different compilation phases.

## Usage

```bash
./scripts/ziku-test.sh <phase> <expression-or-file>
```

### Phases

| Phase | Description |
|-------|-------------|
| `parse` | Show parsed AST |
| `infer` | Run type inference, show inferred type |
| `eval` | Evaluate via IR interpreter |
| `translate` | Show IR translation |
| `scheme` | Generate Scheme code |
| `scheme-run` | Generate and run Scheme code |

### Examples

```bash
# Type inference
./scripts/ziku-test.sh infer 'let x = 1 in x + 1'

# Evaluation
./scripts/ziku-test.sh eval 'let f = \x => x * 2 in f 5'

# From file
./scripts/ziku-test.sh eval tests/golden/ir-eval/success/arithmetic.ziku

# Generate and run Scheme
./scripts/ziku-test.sh scheme-run 'let x = 1 in x + 1'
```

## Workflow

1. Run the test: `./scripts/ziku-test.sh <phase> <input>`
   - The script automatically builds if needed
2. Analyze output for errors or unexpected behavior

## Common Debugging Scenarios

### Type Inference Issues
```bash
# Check what type is inferred
./scripts/ziku-test.sh infer '\r => r.x'
# Output: ({ x : _t1 | _t2 } -> _t1)

# Check polymorphic function usage
./scripts/ziku-test.sh infer 'let id = \x => x in id 1'
# Output: Int
```

### IR Translation Issues
```bash
# See the generated IR
./scripts/ziku-test.sh translate 'let x = 1 in x + 1'
```

### Evaluation Issues
```bash
# Compare eval result with expected
./scripts/ziku-test.sh eval 'let rec f = \n => if n == 0 then 1 else n * f (n - 1) in f 5'
# Output: 120
```

### Scheme Code Generation
```bash
# Generate and inspect Scheme code
./scripts/ziku-test.sh scheme 'let x = 1 in x + 1'

# Generate and execute Scheme code
./scripts/ziku-test.sh scheme-run 'let x = 1 in x + 1'
```

---
description: Test and debug Ziku expressions through compilation phases. Use when user asks to "test an expression", "check type inference", "debug evaluation", "see IR translation", or "generate Scheme code". (project)
---

# Ziku Test Skill

Test and debug Ziku expressions through different compilation phases.

## Usage

```bash
lake exe ziku-test <phase> <expression-or-file>
```

### Phases

| Phase | Description |
|-------|-------------|
| `parse` | Show parsed AST |
| `infer` | Run type inference, show inferred type |
| `eval` | Evaluate via IR interpreter |
| `translate` | Show IR translation |
| `scheme` | Generate Scheme code |

### Examples

```bash
# Type inference
lake exe ziku-test infer 'let x = 1 in x + 1'

# Evaluation
lake exe ziku-test eval 'let f = \x => x * 2 in f 5'

# From stdin
echo 'let x = { a = 1 } in x.a' | lake exe ziku-test infer

# From file
lake exe ziku-test eval tests/golden/ir-eval/success/arithmetic.ziku
```

## Workflow

1. Build if needed: `lake build`
2. Run the test: `lake exe ziku-test <phase> <input>`
3. Analyze output for errors or unexpected behavior

## Common Debugging Scenarios

### Type Inference Issues
```bash
# Check what type is inferred
lake exe ziku-test infer '\r => r.x'
# Output: ({ x : _t1 | _t2 } -> _t1)

# Check polymorphic function usage
lake exe ziku-test infer 'let id = \x => x in id 1'
# Output: Int
```

### IR Translation Issues
```bash
# See the generated IR
lake exe ziku-test translate 'let x = 1 in x + 1'
```

### Evaluation Issues
```bash
# Compare eval result with expected
lake exe ziku-test eval 'let rec f = \n => if n == 0 then 1 else n * f (n - 1) in f 5'
# Output: 120
```

### Scheme Code Generation
```bash
# Generate and inspect Scheme code
lake exe ziku-test scheme 'let x = 1 in x + 1'
```

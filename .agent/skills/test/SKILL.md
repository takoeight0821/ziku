---
description: Test and debug Ziku expressions through compilation phases. Use when user asks to "test an expression", "check type inference", "debug evaluation", "see IR translation", or "generate Scheme code". (project)
---

# Ziku Test Skill

Test and debug Ziku expressions through different compilation phases using Docker via mise.

## Usage

```bash
mise run docker:run <phase> <expression-or-file>
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
mise run docker:run infer 'let x = 1 in x + 1'

# Evaluation
mise run docker:run eval 'let f = \x => x * 2 in f 5'

# From file
mise run docker:run eval tests/golden/ir-eval/success/arithmetic.ziku

# Generate Scheme code
mise run docker:run scheme 'let x = 1 in x + 1'
```

## Running Tests via Docker (mise)

```bash
mise run docker:test                     # Run all tests
mise run docker:test:category infer      # Run specific category
mise run docker:build-check              # Check build
mise run docker:infer <file>             # Infer type of a .ziku file
```

## Common Debugging Scenarios

### Type Inference Issues
```bash
# Check what type is inferred
mise run docker:run infer '\r => r.x'
# Output: ({ x : _t1 | _t2 } -> _t1)

# Check polymorphic function usage
mise run docker:run infer 'let id = \x => x in id 1'
# Output: Int
```

### IR Translation Issues
```bash
# See the generated IR
mise run docker:run translate 'let x = 1 in x + 1'
```

### Evaluation Issues
```bash
# Compare eval result with expected
mise run docker:run eval 'let rec f = \n => if n == 0 then 1 else n * f (n - 1) in f 5'
# Output: 120
```

### Scheme Code Generation
```bash
# Generate and inspect Scheme code
mise run docker:run scheme 'let x = 1 in x + 1'
```

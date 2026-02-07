---
description: Add golden tests to the Ziku test suite. Use when user asks to "add a test", "create a golden test", "test this expression", "add regression test", or "try a simpler case".
---

# Adding Golden Tests

Golden tests compare actual output against expected output stored in `.golden` files.

## Quick Start

1. Create test file: `tests/golden/{category}/{success|error}/{name}.ziku`
2. Run `lake test` to auto-generate `.golden` file
3. Verify the generated `.golden` file is correct
4. Commit both `.ziku` and `.golden` files

## Test Categories

| Category | Purpose | Example Use Case |
|----------|---------|------------------|
| `parser` | Parser output | Syntax edge cases, error recovery |
| `infer` | Type inference | Polymorphism, record types, error messages |
| `ir-eval` | IR interpreter | Expression evaluation, recursion |
| `scheme` | Scheme codegen | Code generation correctness |
| `scheme-only` | Direct Scheme execution | Scheme runtime behavior |
| `io` | IO operations | Print, input handling |
| `truncate` | Truncated evaluation | Big-step semantics testing |
| `big-step` | Big-step semantics | Alternative evaluator |
| `consistency` | Cross-evaluator consistency | Same result across evaluators |

## Directory Structure

```
tests/golden/
├── parser/
│   ├── success/       # Valid syntax tests
│   │   ├── simple.ziku
│   │   └── simple.golden
│   └── error/         # Parse error tests
│       ├── missing-paren.ziku
│       └── missing-paren.golden
├── infer/
│   ├── success/       # Type inference success
│   └── error/         # Type errors
├── ir-eval/
│   ├── success/       # Evaluation tests
│   └── error/         # Runtime errors
└── ...
```

## Workflow

### Adding a Success Test

```bash
# 1. Create test file
echo 'let x = 1 in x + 1' > tests/golden/ir-eval/success/simple-let.ziku

# 2. Run tests to generate golden file
lake test -- ir-eval

# 3. Check generated golden file
cat tests/golden/ir-eval/success/simple-let.golden
# Output: 2

# 4. If correct, commit both files
```

### Adding an Error Test

```bash
# 1. Create test file with expected-to-fail code
echo 'let x = true in x + 1' > tests/golden/infer/error/type-mismatch.ziku

# 2. Run tests to generate golden file
lake test -- infer

# 3. Verify error message is correct
cat tests/golden/infer/error/type-mismatch.golden
# Output: Type error: expected Int, got Bool

# 4. Commit both files
```

### Debugging with Simpler Cases

When debugging complex issues, add a simpler test case:

```bash
# Original failing case is complex
# Add simpler reproduction
echo '\x => x' > tests/golden/infer/success/identity-simple.ziku
lake test -- infer
```

## Test Execution Commands

```bash
# Docker (recommended - no local dependencies)
mise run docker:test                     # Run all tests
mise run docker:test:category infer      # Run specific category

# Native (requires Lean 4 + Chez Scheme)
lake test                                # Run all tests
lake test -- parser                      # Run specific category
lake test -- parser infer                # Run multiple categories

# Parallel execution (native, recommended for full runs)
make -j4 test-parallel

# Fast tests only (parser, infer, truncate, big-step)
make -j4 test-fast

# Show available categories
lake test -- --help
```

## Writing Effective Tests

### Good Test Characteristics

- **Minimal**: Smallest code that demonstrates the behavior
- **Focused**: Tests one thing at a time
- **Named descriptively**: `record-projection.ziku`, not `test1.ziku`

### Test Naming Convention

```
{feature}-{variant}.ziku

Examples:
- let-simple.ziku
- let-nested.ziku
- let-polymorphic.ziku
- function-application.ziku
- function-higher-order.ziku
```

### Testing Edge Cases

| Feature | Edge Cases to Test |
|---------|-------------------|
| Arithmetic | Negative numbers, zero, large numbers |
| Functions | Currying, partial application, recursion |
| Records | Empty record, single field, nested |
| Pattern match | Exhaustiveness, nested patterns |
| Polymorphism | Instantiation, let-polymorphism |

## Checklist

When adding a golden test:

- [ ] Chose appropriate category
- [ ] Used descriptive file name
- [ ] Test is minimal (no unnecessary code)
- [ ] Verified `.golden` file content is correct
- [ ] Committed both `.ziku` and `.golden` files

## References

- [CLAUDE.md#testing](../../CLAUDE.md) - Testing overview
- [tests/golden/](../../tests/golden/) - Existing tests as examples
- [/test skill](../test/SKILL.md) - Interactive testing workflow

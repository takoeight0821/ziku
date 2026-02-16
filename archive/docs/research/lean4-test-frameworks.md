# Lean 4 Test Frameworks

Research on testing frameworks and approaches available for Lean 4 projects.

## Overview

Lean 4 provides multiple testing approaches ranging from built-in commands to dedicated frameworks. The main options are:

| Framework | Type | Integration | Best For |
|-----------|------|-------------|----------|
| `#guard` | Built-in assertion | Compile-time | Simple checks |
| LSpec | Unit testing framework | Lake `@[test_driver]` | Structured test suites |
| SlimCheck | Property-based testing | Via LSpec or Mathlib4 | Randomized testing |
| Golden tests | Snapshot testing | Custom executables | Parser/compiler output |

## Built-in `#guard` Command

Lean 4's native testing support via the `#guard` command.

### Features

- Checks if expressions evaluate to `true`
- Uses untrusted evaluator (no proof generated)
- Expression must be decidable
- **Fails at compile time** if guard fails

### Basic Usage

```lean
#guard 1 + 1 = 2
#guard [1, 2, 3].length = 3
#guard "hello".length = 5
```

### Working with Except Types

For functions returning `Except`, you need `DecidableEq`:

```lean
def Except.deq [DecidableEq α] [DecidableEq β] : DecidableEq (Except α β)
  | .ok a, .ok b => if h : a = b then isTrue (by simp [h]) else isFalse (by simp [h])
  | .error a, .error b => if h : a = b then isTrue (by simp [h]) else isFalse (by simp [h])
  | .ok _, .error _ => isFalse (by simp)
  | .error _, .ok _ => isFalse (by simp)

instance [DecidableEq α] [DecidableEq β] : DecidableEq (Except α β) := Except.deq

-- Now you can use:
#guard myFunction arg = Except.ok expectedResult
```

### Pros and Cons

**Pros:**
- No external dependencies
- Immediate feedback during development
- Simple syntax

**Cons:**
- No test organization/grouping
- No detailed failure messages
- Cannot run subset of tests

## LSpec Framework

The primary testing framework for Lean 4, inspired by Haskell's Hspec.

- **Repository**: [github.com/lurk-lab/LSpec](https://github.com/lurk-lab/LSpec)
- **License**: MIT
- **Stars**: 66 | **Forks**: 12
- **Language**: 97.8% Lean, 2.2% Nix

### Installation

Add to `lakefile.lean`:

```lean
require LSpec from git
  "https://github.com/lurk-lab/LSpec.git" @ "main"
```

### Core API

#### TestSeq Datatype

Tests are composed using `TestSeq` with the `test` helper:

```lean
import LSpec

#lspec
  test "addition works" (1 + 1 = 2) $
  test "list length" ([1, 2, 3].length = 3) $
  done
```

#### Testable Typeclass

The `Testable` typeclass determines how propositions are evaluated:

```lean
class Testable (p : Prop) where
  test : TestResult
```

Custom instances return `.isTrue` with proof or `.isFalse` with optional failure message.

### Interactive Testing: `#lspec`

Run tests directly in files with immediate feedback:

```lean
#lspec
  test "basic arithmetic" (2 * 3 = 6) $
  test "string concat" ("a" ++ "b" = "ab") $
  done
```

**Behavior:**
- Failing tests interrupt the build process
- Errors shown inline in IDE
- Great for TDD workflow

### Compiled Testing: `lspecIO`

For CI/CD integration:

```lean
-- Tests/MyTests.lean
import LSpec

def myTests : TestSeq :=
  test "test 1" (1 = 1) $
  test "test 2" (2 = 2) $
  done

def main : IO UInt32 := do
  lspecIO [("My Test Suite", myTests)]
```

In `lakefile.lean`:

```lean
@[test_driver]
lean_exe tests where
  root := `Tests.MyTests
```

#### Grouping Tests

```lean
def arithmeticTests : TestSeq :=
  group "arithmetic" $
    test "addition" (1 + 1 = 2) $
    test "multiplication" (2 * 3 = 6) $
    done

def stringTests : TestSeq :=
  group "strings" $
    test "concat" ("a" ++ "b" = "ab") $
    test "length" ("hello".length = 5) $
    done

def main : IO UInt32 := do
  lspecIO [
    ("Arithmetic", arithmeticTests),
    ("Strings", stringTests)
  ]
```

### SlimCheck Integration

LSpec includes property-based testing via SlimCheck:

#### Required Typeclasses

1. **Shrinkable**: Produces "smaller" test cases for counterexample reduction
2. **SampleableExt**: Generates random test inputs (like QuickCheck's Arbitrary)
3. **Checkable**: Marks properties as testable

#### Example

```lean
import LSpec
import LSpec.SlimCheck

-- Property: reversing twice gives original list
#lspec
  check "reverse involutive" fun (xs : List Nat) =>
    xs.reverse.reverse = xs
```

## SlimCheck (Mathlib4)

Property-based testing library in Mathlib4, Lean 4's port of QuickCheck.

### Features

- Randomized testing with shrinking
- Automatic counterexample minimization
- Integration with Lean's type system
- Can admit theorems with `sorry` when no counterexample found

### Status

Part of Mathlib4 but not yet fully released as standalone. Best accessed via LSpec integration.

### Usage Pattern

```lean
import Mathlib.Testing.SlimCheck

-- Define properties as functions returning Bool or Prop
def prop_reverse_length (xs : List Nat) : Bool :=
  xs.reverse.length = xs.length

-- SlimCheck will generate random inputs and test
```

## Golden Testing

File-based comparison testing (what Ziku currently uses).

### Structure

```
tests/golden/
├── parser/
│   ├── test1.ziku
│   └── test1.golden
├── eval/
│   ├── test2.ziku
│   └── test2.golden
└── ir-eval/
    ├── test3.ziku
    └── test3.golden
```

### Implementation Pattern

```lean
-- GoldenTest.lean
def runGoldenTest (category : String) (name : String) : IO Bool := do
  let input ← IO.FS.readFile s!"tests/golden/{category}/{name}.ziku"
  let result := process input  -- your processing function
  let expected ← IO.FS.readFile s!"tests/golden/{category}/{name}.golden"
  return result.trim = expected.trim
```

### Pros and Cons

**Pros:**
- Easy to add new tests
- Human-readable expected output
- Good for compiler/parser testing
- Auto-generate `.golden` files on first run

**Cons:**
- Brittle to formatting changes
- No isolation between tests
- Manual test registration needed

## Lean 4 Internal Test Suite

How the Lean 4 compiler itself is tested (useful for reference).

### Test Categories

| Directory | Purpose |
|-----------|---------|
| `tests/lean` | Output comparison with `.expected.out` files |
| `tests/lean/run` | Exit code only, no output check |
| `tests/lean/interactive` | Server request testing with position markers |
| `tests/lean/server` | Lean `--server` protocol tests |
| `tests/compiler` | Compilation and executable tests |
| `tests/bench` | Performance benchmarks |

### Best Practices from Lean Team

1. Every test file should include:
   - Initial `/-! -/` docstring summarizing purpose
   - Section docstrings explaining what is tested

2. Test repair workflow:
   ```bash
   # Compare and update expected output
   ./test_single.sh -i test_name.lean

   # Bulk update all .expected.out files
   tests/lean/copy-produced
   ```

## Recommendations for Ziku

Based on this research, here are recommendations for Ziku:

### Current Setup (Golden Tests)

Your current golden test approach is good for:
- Parser output verification
- Evaluation result checking
- IR translation validation

### Suggested Additions

1. **Add `#guard` for quick inline checks:**
   ```lean
   -- In Ziku/IR/Eval.lean
   #guard eval (Producer.lit (Lit.int 42)) = Value.int 42
   ```

2. **Consider LSpec for unit tests:**
   - Test individual functions in isolation
   - Better failure messages
   - Organized test suites

3. **Property-based testing for language semantics:**
   - Test that translation preserves semantics
   - Test type inference properties
   - Random expression generation

### Migration Path

1. Keep golden tests for integration/snapshot testing
2. Add `#guard` checks inline during development
3. Add LSpec for comprehensive unit testing
4. Consider SlimCheck for property-based tests of core invariants

## Sources

- [LSpec GitHub Repository](https://github.com/lurk-lab/LSpec)
- [Lean 4 Testing Documentation](https://github.com/leanprover/lean4/blob/master/doc/dev/testing.md)
- [Writing Unit Tests in Lean 4 - Brandon Rozek](https://brandonrozek.com/blog/writing-unit-tests-lean-4/)
- [Lean 4 Community Discussion on Testing](https://leanprover-community.github.io/archive/stream/270676-lean4/topic/simple.20interactive.20unit.20testing.3F.html)
- [SlimCheck Demo - Northeastern](https://course.ccs.neu.edu/cs2800sp23/l37.html)

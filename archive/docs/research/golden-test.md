# Golden Test (Snapshot Testing)

## Overview

Golden testing (also known as snapshot testing, golden master testing, or characterization testing) is a testing methodology where test outputs are compared against pre-recorded "golden" reference files rather than hardcoded expected values.

## How It Works

1. **First Run**: The test executes and saves its output to a file (the "golden" file)
2. **Subsequent Runs**: The test compares current output against the golden file
3. **Pass/Fail**: Test passes if outputs match, fails if they differ
4. **Update**: When changes are intentional, golden files can be regenerated

```
Input File (.ziku)     →  Parser/Compiler  →  Output
                                               ↓
                                          Compare
                                               ↓
Golden File (.golden)  ←←←←←←←←←←←←←←←←←  Match?
```

## Key Benefits

### 1. Easy to Write
- No need to manually construct expected outputs
- Just run the test and accept the output as the golden standard
- Especially useful for complex outputs (AST, IR, error messages)

### 2. Good for Legacy Code
- Can test code without fully understanding it
- Capture current behavior as a baseline
- Detect unintended changes during refactoring

### 3. Rich Test Data
- Full textual representation of outputs
- Easier to debug when tests fail
- Git diffs show exactly what changed

### 4. Adaptable
- Easy to update when behavior changes intentionally
- Single command to regenerate all golden files

## Common Drawbacks

1. **Fragility**: Small formatting changes can break many tests
2. **Maintenance Overhead**: Many files to manage
3. **False Confidence**: Tests may pass even with subtle bugs
4. **Review Burden**: Must carefully verify golden file updates

## Implementation Patterns

### Directory Structure

```
tests/
├── golden/
│   ├── arithmetic/
│   │   ├── add.ziku          # Input
│   │   └── add.golden        # Expected output
│   ├── parser/
│   │   ├── lambda.ziku
│   │   └── lambda.golden
│   └── errors/
│       ├── undefined.ziku
│       └── undefined.golden
```

### Typical Workflow

```bash
# Run tests
./run-tests.sh

# If intentional changes, update golden files
./run-tests.sh --accept
```

### Haskell: tasty-golden

```haskell
import Test.Tasty
import Test.Tasty.Golden

main = defaultMain $ testGroup "Parser Tests"
  [ goldenVsString "arithmetic" "test/arithmetic.golden" $
      return $ parseAndPrint "1 + 2 * 3"
  ]
```

### Simple Shell Script Approach

```bash
#!/bin/bash
for input in tests/*.ziku; do
  golden="${input%.ziku}.golden"
  output=$(./ziku < "$input")

  if [ "$1" = "--accept" ]; then
    echo "$output" > "$golden"
  elif ! diff -q <(echo "$output") "$golden" > /dev/null; then
    echo "FAIL: $input"
    diff <(echo "$output") "$golden"
  fi
done
```

## Use Cases for Compilers/Interpreters

### 1. Parser Output (AST)
```
-- Input: let.ziku
let x = 1 in x + 1

-- Golden: let.golden
Let "x" (Lit 1) (BinOp Add (Var "x") (Lit 1))
```

### 2. Type Inference Results
```
-- Input: infer.ziku
\x => x + 1

-- Golden: infer.golden
Int -> Int
```

### 3. Error Messages
```
-- Input: error.ziku
x + 1

-- Golden: error.golden
Error at 1:1: undefined variable 'x'
```

### 4. Compiled Output / IR
```
-- Input: compile.ziku
let f = \x => x * 2 in f 21

-- Golden: compile.golden
PUSH 21
CALL f
...
```

### 5. Evaluation Results
```
-- Input: eval.ziku
1 + 2 * 3

-- Golden: eval.golden
7
```

## Libraries and Tools

### Haskell
- [tasty-golden](https://hackage.haskell.org/package/tasty-golden) - Golden tests for tasty framework
- [hspec-golden](https://hackage.haskell.org/package/hspec-golden) - Golden tests for hspec

### Other Languages
- **Rust**: `insta` crate for snapshot testing
- **Go**: [golden](https://github.com/franiglesias/golden) library
- **JavaScript**: Jest snapshot testing
- **Python**: `pytest-snapshot`

## Best Practices

1. **Organize by Feature**: Group related tests together
2. **Descriptive Names**: Use meaningful file names
3. **Version Control**: Track golden files in git
4. **Review Diffs**: Carefully review golden file changes in PRs
5. **Stable Output**: Avoid timestamps, random values in output
6. **Normalize Output**: Sort unordered outputs for consistency

## Relation to Other Testing Methods

| Method | When to Use |
|--------|-------------|
| Unit Tests | Testing small, pure functions with known outputs |
| Golden Tests | Testing complex outputs, parsers, compilers |
| Property Tests | Finding edge cases through random generation |
| Integration Tests | Testing system interactions |

## Sources

- [Snapshot testing in practice: Benefits and drawbacks](https://www.sciencedirect.com/science/article/abs/pii/S0164121223001929)
- [Snapshot Testing For the Masses - TigerBeetle](https://tigerbeetle.com/blog/2024-05-14-snapshot-testing-for-the-masses/)
- [Golden tests are tasty - Kwang's Haskell Blog](https://kseo.github.io/posts/2016-12-15-golden-tests-are-tasty.html)
- [tasty-golden - Hackage](https://hackage.haskell.org/package/tasty-golden)
- [What is the Golden Master Technique](https://stevenschwenke.de/whatIsTheGoldenMasterTechnique)
- [Golden Tests - Medium](https://medium.com/casperblockchain/golden-tests-e521077ae235)

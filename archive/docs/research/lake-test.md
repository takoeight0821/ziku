# Lake Test: Testing Infrastructure for Lean 4 Projects

## Overview

- **Command**: `lake test`
- **Lake Version**: 5.0.0 (Lean 4.26.0)
- **Documentation**: [Lake Reference](https://lean-lang.org/doc/reference/latest/Build-Tools-and-Distribution/Lake/)

## Summary

`lake test` is Lake's built-in command for running tests in Lean 4 projects. It executes a **test driver** that can be a script, executable, or library.

## Configuration

### Package-Level Options

| Option | Type | Description |
|--------|------|-------------|
| `testDriver` | `String` | Name of the script, executable, or library to run |
| `testDriverArgs` | `Array String` | Arguments passed to the driver before CLI args |

### lakefile.toml Format

```toml
name = "myproject"
version = "0.1.0"
defaultTargets = ["myproject"]
testDriver = "tests"           # Reference the executable name
testDriverArgs = ["--verbose"] # Optional arguments

[[lean_lib]]
name = "MyProject"

[[lean_exe]]
name = "tests"
root = "Tests.Main"
```

### lakefile.lean Format

Use the `@[test_driver]` attribute:

```lean
package myproject where
  -- package options

@[test_driver]
lean_exe tests where
  root := `Tests.Main
```

Or set `testDriver` explicitly:

```lean
package myproject where
  testDriver := "tests"
  testDriverArgs := #["--verbose"]

lean_exe tests where
  root := `Tests.Main
```

### Referencing Dependencies

To use a test driver from a dependency:

```toml
testDriver = "dependency-pkg/testRunner"
```

## Driver Types

| Type | Behavior |
|------|----------|
| **Executable** | Built, then executed with `testDriverArgs` + CLI args |
| **Script** | Executed with `testDriverArgs` + CLI args |
| **Library** | Built only (tests run via elaboration-time errors) |

## Usage

```bash
# Run tests
lake test

# Pass additional arguments
lake test -- --filter "pattern"

# Check if test driver is configured (no output = success)
lake check-test
```

## Current Issue with ziku Project

The current `lakefile.toml` has an invalid `[[test]]` section:

```toml
[[test]]
name = "golden-test"
driver = "{buildDir}/bin/golden-test"
```

This `[[test]]` syntax is **not recognized** by Lake. The correct configuration should be:

```toml
name = "ziku"
version = "0.1.0"
defaultTargets = ["ziku"]
testDriver = "golden-test"      # Add this line

[[lean_lib]]
name = "Ziku"

[[lean_exe]]
name = "ziku"
root = "Main"

[[lean_exe]]
name = "golden-test"
root = "tests.GoldenTest"
```

## Library-Based Testing

For tests that should fail at elaboration time (common in theorem provers):

```lean
@[test_driver]
lean_lib TestLib where
  -- Tests are run during compilation
  -- Elaboration errors indicate test failures
```

## Real-World Examples

### mathlib4

Uses `testDriver := "MathlibTest"` in [lakefile.lean](https://github.com/leanprover-community/mathlib4/blob/master/lakefile.lean).

### loogle

Uses `testDriver := "Tests"` in [lakefile.lean](https://github.com/nomeata/loogle/blob/master/lakefile.lean).

## Related Commands

| Command | Description |
|---------|-------------|
| `lake test` | Run the configured test driver |
| `lake check-test` | Verify test driver configuration |
| `lake lint` | Run the lint driver (similar mechanism) |
| `lake build` | Build targets (prerequisite for testing) |

## Sources

- [Lake Documentation](https://lean-lang.org/doc/reference/latest/Build-Tools-and-Distribution/Lake/)
- [Lake README (GitHub)](https://github.com/leanprover/lean4/blob/master/src/lake/README.md)
- [Lake CLI Help](https://github.com/leanprover/lean4/blob/master/src/lake/Lake/CLI/Help.lean)
- [Package Configuration Source](https://github.com/leanprover/lean4/blob/master/src/lake/Lake/Config/Package.lean)
- [mathlib4 lakefile](https://github.com/leanprover-community/mathlib4/blob/master/lakefile.lean)

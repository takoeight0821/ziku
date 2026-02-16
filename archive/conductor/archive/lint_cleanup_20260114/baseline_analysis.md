# Lint Warning Baseline Analysis

**Date:** 2026-01-14
**Total Warnings:** ~30 (Estimated based on output)

## Categories

### 1. Deprecated String Methods (Major)
The vast majority of warnings are due to recent Lean 4 standard library updates deprecating certain `String` methods in favor of more explicit Unicode/ASCII variants or differently named functions.

- **`String.trim` -> `String.trimAscii`**
  - The compiler notes: "The updated constant has a different type: `String → String.Slice` instead of `String → String`". This implies we might need to convert the resulting `Substring` (alias for `String.Slice`) back to `String` using `.toString` if the code expects a `String`.
  - **Locations:**
    - `Main.lean`
    - `Backend/SchemeMain.lean`
    - `ZikuTest.lean`
    - `tests/EmitCompiledCode.lean`
    - `tests/TestRunner.lean`

- **`String.dropRight` -> `String.dropEnd`**
  - **Locations:**
    - `tests/EmitCompiledCode.lean`
    - `tests/TestRunner.lean`

### 2. Unused Variables (Minor)
A few instances of unused variables in the test runner.

- **`unused variable name`**
  - `tests/TestRunner.lean:359:31`
- **`unused variable baseName`**
  - `tests/TestRunner.lean:647:15`

## Action Plan
1.  **Prioritize Deprecations:** These are the most numerous. Replacing them will clear up the build output significantly. Attention must be paid to the return type change (`String` -> `Substring`).
2.  **Fix Unused Variables:** Simple deletion or renaming to `_` if needed for pattern matching.

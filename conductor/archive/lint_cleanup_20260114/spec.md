# Specification: Linting Improvements and Error Resolution

## Overview
This track focuses on improving the code health of the Ziku project by resolving existing lint warnings and errors, and subsequently tightening the project's linting configuration to maintain a high standard of code quality.

## Objectives
- Investigate and resolve all current warnings and errors produced by `lake test` and the Lean 4 compiler.
- Address a wide range of issues including unused variables, formatting/style inconsistencies, type/logic concerns, and missing documentation.
- Configure additional Lean 4 built-in linters in `lakefile.lean` to prevent future regressions.

## Functional Requirements
- **Error Resolution:**
    - Fix all "unused variable" and "unused import" warnings.
    - Resolve any type mismatches or logical warnings flagged by the compiler.
    - Ensure all pattern matches are exhaustive where practical, or explicitly handled.
- **Style & Formatting:**
    - Standardize code formatting across the project (indentation, naming conventions).
- **Documentation:**
    - Add docstrings to public functions and types where flagged by `missingDocs` or similar linters.
- **Linter Configuration:**
    - Update `lakefile.lean` to enable a stricter set of built-in Lean 4 linters.

## Non-Functional Requirements
- **Maintainability:** The resulting codebase should be cleaner and easier to navigate.
- **Case-by-Case Handling:** For complex components like the evaluator (`IR/Eval.lean`) or interpreter, the `partial` keyword is acceptable if termination proofs are impractical, but should be documented.

## Acceptance Criteria
- `lake test` runs with zero warnings or errors (excluding accepted `partial` usages).
- `lake build` completes successfully without any warnings.
- `lakefile.lean` contains an expanded set of enabled linters.
- New code follows the project's established style guides.

## Out of Scope
- Major architectural refactoring unrelated to linting issues.
- Migrating the entire codebase to be provably terminating (we will handle `partial` on a case-by-case basis).
- Implementing a completely new CI environment (focusing on local configuration first).

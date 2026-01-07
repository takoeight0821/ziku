# Specification: MAL Step 3 - Persistence and `def!`

## Overview
This track implements the `def!` special form in the Ziku MAL implementation and refactors the evaluator to return both a value and an updated environment. This change is crucial for supporting persistent definitions, where a binding created by `def!` remains available for subsequent evaluations.

## Functional Requirements
1.  **Evaluator Refactor**: Change the `eval` function signature from `eval(env, ast) -> value` to `eval(env, ast) -> Pair(value, updated_env)`.
2.  **`def!` Special Form**: Implement handling for `(def! symbol value)`.
    -   It should evaluate `value` in the current environment.
    -   It should bind the resulting value to `symbol` in the *current* environment (topmost scope).
    -   It should return the evaluated value and the environment containing the new binding.
3.  **`let*` Update**: Update the `let*` implementation to use the new `eval` signature. Note that `let*` bindings remain local to the `let*` body.
4.  **Persistent Binding Tests**: Create a test case that demonstrates a `def!` binding being accessed by a subsequent expression.

## Acceptance Criteria
-   Executing `(def! a 10)` returns `Pair(MNum(10), updated_env)`.
-   A subsequent evaluation using `updated_env` for the symbol `a` returns `MNum(10)`.
-   The golden test `mal_step3_def.ziku` correctly demonstrates this persistence.

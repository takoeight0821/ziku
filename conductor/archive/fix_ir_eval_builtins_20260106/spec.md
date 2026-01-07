# Specification: Fix IR Evaluator Stuck on Builtins

## 1. Overview
The IR evaluator (`Ziku.IR.Eval`) fails to make progress (gets "stuck") when evaluating `Statement.builtin` calls where arguments are variables bound in the environment. This specifically impacts deep CPS contexts (like `mal_step5_tco_fn.ziku`).

## 2. Problem Statement
`evalBuiltin` only accepts literal values. When it encounters a variable argument (common in function bodies), the evaluator attempts to "force" it via a reduction step. This forcing mechanism appears to fail or loop in complex CPS scenarios, causing the evaluator to halt.

## 3. Goals
- Fix the `ir-eval` "stuck" state for builtins with variable arguments.
- Enable `mal_step5_tco_fn.ziku` to pass as an IR evaluation test.
- Refactor `evalBuiltin` to directly resolve variables from the environment.

## 4. Functional Requirements
- **Refactor `evalBuiltin`**: Update signature to `Builtin → List Producer → Env → Option Producer`.
- **Direct Lookup**: Inside `evalBuiltin`:
  - If an argument is a literal, use it.
  - If an argument is a `.var`, look it up in the `Env`.
    - If the lookup yields a **closure** containing a literal producer, use that literal.
    - If the lookup yields a non-literal (e.g., another variable or complex producer), fail (return `none` or handle recursively if simple).
  - Otherwise, fail (return `none`).
- **Simplify `stateStep`**: Remove the logic that attempts to "force" builtin arguments by creating new cuts.
- **Test Case**: Move `tests/golden/scheme/success/mal_step5_tco_fn.ziku` to `tests/golden/ir-eval/success/`.

## 5. Non-Functional Requirements
- **No Regressions**: Existing `ir-eval` tests must pass.

## 6. Acceptance Criteria
- [ ] `evalBuiltin` takes `Env` and resolves variables.
- [ ] `mal_step5_tco_fn.ziku` passes in `ir-eval`.
- [ ] All existing tests pass.

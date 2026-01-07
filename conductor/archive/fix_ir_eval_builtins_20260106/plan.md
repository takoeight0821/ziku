# Plan: Fix IR Evaluator Stuck on Builtins

This plan addresses the issue where the IR evaluator gets stuck on builtin functions when arguments are variables bound in the environment.

## Phase 1: Preparation and Regression Test [checkpoint: 0274987]
- [x] Task: Move reproduction case `tests/golden/scheme/success/mal_step5_tco_fn.ziku` to `tests/golden/ir-eval/success/` [9145017]
- [x] Task: Run tests to confirm failure in `ir-eval` [9145017]
- [x] Task: Conductor - User Manual Verification 'Phase 1: Preparation and Regression Test' (Protocol in workflow.md) [0274987]

## Phase 2: Refactor `evalBuiltin` and `stateStep` [checkpoint: a371a9c]
...
## Phase 3: Verification and Cleanup [checkpoint: a371a9c]
- [x] Task: Run all golden tests to ensure no regressions [2544a1e]
- [x] Task: Verify `mal_step5_tco_fn.ziku` passes in `ir-eval` [2544a1e]
- [x] Task: Conductor - User Manual Verification 'Phase 3: Verification and Cleanup' (Protocol in workflow.md) [2544a1e]

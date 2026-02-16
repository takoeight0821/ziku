# Plan: Fix IR Evaluator Stuck on Complex Patterns

This plan outlines the refactoring of the IR evaluator to an environment-based model to resolve code explosion and "stuck" states.

## Phase 1: Infrastructure and Basic Environment [checkpoint: 76f99e1]

- [x] Task: Define \`Value\` and \`Env\` types in \`Ziku/IR/Eval.lean\` 25027df
- [x] Task: Implement basic environment lookup and extension functions 25027df
- [x] Task: Conductor - User Manual Verification 'Phase 1: Infrastructure and Basic Environment' (Protocol in workflow.md)

## Phase 2: Refactor Evaluator Core

- [x] Task: Modify `EvalResult` to support environment-carrying values d13395d
- [x] Task: Update $\mu$ and $\mũ$ reduction rules to use environments
- [x] Task: Update `cocase` and `case` reduction to use environments
- [x] Task: Conductor - User Manual Verification 'Phase 2: Refactor Evaluator Core' (Protocol in workflow.md)

## Phase 3: Verification and Optimization

- [x] Task: Verify fix with `mal_step3_eval.ziku`
- [x] Task: Ensure all existing golden tests pass
- [x] Task: Performance benchmarking and fuel limit adjustment if necessary
- [x] Task: Conductor - User Manual Verification 'Phase 3: Verification and Optimization' (Protocol in workflow.md)

# Plan: Fix IR Evaluator Stuck on Complex Patterns

This plan outlines the refactoring of the IR evaluator to an environment-based model to resolve code explosion and "stuck" states.

## Phase 1: Infrastructure and Basic Environment

- [ ] Task: Define `Value` and `Env` types in `Ziku/IR/Eval.lean`
- [ ] Task: Implement basic environment lookup and extension functions
- [ ] Task: Conductor - User Manual Verification 'Phase 1: Infrastructure and Basic Environment' (Protocol in workflow.md)

## Phase 2: Refactor Evaluator Core

- [ ] Task: Modify `EvalResult` to support environment-carrying values
- [ ] Task: Update $\mu$ and $\mũ$ reduction rules to use environments
- [ ] Task: Update `cocase` and `case` reduction to use environments
- [ ] Task: Conductor - User Manual Verification 'Phase 2: Refactor Evaluator Core' (Protocol in workflow.md)

## Phase 3: Verification and Optimization

- [ ] Task: Verify fix with `mal_step3_eval.ziku`
- [ ] Task: Ensure all existing golden tests pass
- [ ] Task: Performance benchmarking and fuel limit adjustment if necessary
- [ ] Task: Conductor - User Manual Verification 'Phase 3: Verification and Optimization' (Protocol in workflow.md)

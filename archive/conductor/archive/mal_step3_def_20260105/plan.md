# Plan: MAL Step 3 - Persistence and `def!`

## Phase 1: Architecture Refactor [checkpoint: c2a288e]
- [x] Task: Update Eval Signature (913cff6)
    - [x] Sub-task: Modify `eval` to return `Pair(value, new_env)`.
    - [x] Sub-task: Update `evalList` helper to thread the environment if needed.
- [x] Task: Conductor - User Manual Verification 'Phase 1' (Protocol in workflow.md)

## Phase 2: Feature Implementation [checkpoint: c2a288e]
- [x] Task: Implement `def!` (913cff6)
    - [x] Sub-task: Add `def!` case to `eval`.
    - [x] Sub-task: Implement logic to evaluate the value and update the environment.
- [x] Task: Update `let*` (913cff6)
    - [x] Sub-task: Adapt `let*` logic to the new `eval` return type.
- [x] Task: Conductor - User Manual Verification 'Phase 2' (Protocol in workflow.md)

## Phase 3: Verification [checkpoint: c2a288e]
- [x] Task: Create Golden Test (913cff6)
    - [x] Sub-task: Create `tests/golden/ir-eval/success/mal_step3_def.ziku` demonstrating sequential `def!` and lookup.
- [x] Task: Run Tests (913cff6)
    - [x] Sub-task: Execute `lake test` and verify golden output.
- [x] Task: Conductor - User Manual Verification 'Phase 3' (Protocol in workflow.md)

# Plan: MAL Migration and Official Test System

## Phase 1: Scaffolding and Infrastructure [checkpoint: 9369ad8]
- [x] Task: Create `examples/mal/` directory structure. f16d57c
- [x] Task: Add `kanaka/mal` as a git submodule in `vendor/mal`. 62362a5
- [x] Task: Create `examples/mal/run` shell script (executable wrapper for `lake exe ziku` targeting MAL steps). 8c951da
- [x] Task: Conductor - User Manual Verification 'Phase 1: Scaffolding and Infrastructure' (Protocol in workflow.md)

## Phase 2: Code Migration and Modularization [checkpoint: c897f04]
- [x] Task: Extract Shared Logic: Create `examples/mal/core.ziku` (types, env, common helpers). 4129985
- [x] Task: Migrate Step 0 (REPL): Implement examples/mal/step0_repl.ziku. ce437ed
- [x] Task: Migrate Step 1 (Read & Print): Implement examples/mal/step1_read_print.ziku. 866b0e2
- [x] Task: Migrate Step 2 (Eval): Implement `examples/mal/step2_eval.ziku`. 482cbd6
- [x] Task: Migrate Step 3 (Env): Implement `examples/mal/step3_env.ziku`. da7b6e9
- [x] Task: Migrate Step 4 (If, Fn, Do): Implement `examples/mal/step4_if_fn_do.ziku`. a778741
- [x] Task: Migrate Step 5 (TCO): Implement `examples/mal/step5_tco.ziku`. c415de4
- [ ] Task: Conductor - User Manual Verification 'Phase 2: Code Migration and Modularization' (Protocol in workflow.md)

## Phase 3: Official Test Harness
- [ ] Task: Implement `scripts/run-mal-test.sh` to execute the official MAL test runner (`vendor/mal/runtest.py`) against the Ziku implementation.
- [ ] Task: Verify all steps (0-5) pass the official tests from `vendor/mal/tests/`.
- [ ] Task: Conductor - User Manual Verification 'Phase 3: Official Test Harness' (Protocol in workflow.md)

## Phase 4: Finalization
- [ ] Task: Update `README.md` or create `examples/mal/README.md` with instructions on how to run and test MAL.
- [ ] Task: Remove or archive old MAL test files in `tests/golden/` if they are fully redundant.
- [ ] Task: Conductor - User Manual Verification 'Phase 4: Finalization' (Protocol in workflow.md)

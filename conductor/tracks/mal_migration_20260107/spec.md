# Specification: MAL Migration and Official Test System

## Overview
Migrate the existing MAL (Make a Lisp) implementation from fragmented golden tests into a structured, standalone directory in `examples/mal/`. Additionally, implement a test system capable of running the official [kanaka/mal](https://github.com/kanaka/mal) test suite against the Ziku-based MAL implementation.

## Goals
- **Maintainability**: Centralize MAL logic in `examples/mal/` to avoid duplication across tests.
- **Compliance**: Verify the Ziku implementation against the official MAL test specifications.
- **Portability**: Ensure MAL can be easily run as a standalone Ziku program.

## Functional Requirements
1.  **Code Migration**:
    *   Extract core MAL components (Reader, Evaluator, Printer, Env) into reusable modules in `examples/mal/`.
    *   Provide entry point scripts for each MAL step (e.g., `step0_repl.ziku`, `step1_read_print.ziku`, etc.).
2.  **Official Test Harness**:
    *   Integrate official MAL test files (`.mal`).
    *   Implement a runner (e.g., `scripts/run-mal-tests.sh`) that maps Ziku execution to the MAL test protocol (reading inputs and asserting expected outputs).
3.  **Step-wise Execution**:
    *   Support running tests for specific steps (0 through 5, based on current progress).

## Non-Functional Requirements
- **No Regression**: All logic currently verified by `tests/golden/ir-eval/success/mal_*.ziku` must remain functional.

## Acceptance Criteria
- [ ] `examples/mal/` exists with modularized Ziku source files.
- [ ] `scripts/run-mal-tests.sh` is functional and can execute official MAL tests.
- [ ] All currently implemented MAL steps (up to Step 5 TCO) pass their respective official tests.

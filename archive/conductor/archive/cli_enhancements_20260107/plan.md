# Plan: CLI Enhancements - Help and Script Execution

## Phase 1: Argument Parsing and Help
- [ ] Task: Implement a basic command-line argument parser in `Main.lean`.
- [ ] Task: Add `-h` and `--help` flags to display the usage menu.
- [ ] Task: Write Tests: Verify help output via shell execution.
- [ ] Task: Conductor - User Manual Verification 'Phase 1: Argument Parsing and Help' (Protocol in workflow.md)

## Phase 2: Script and Stdin Execution
- [ ] Task: Implement logic to read from a file path provided as a positional argument.
- [ ] Task: Implement logic to read from standard input when no file is provided and stdin is not a TTY.
- [ ] Task: Write Failing Tests: Create a `.ziku` script and attempt to run it via the CLI, asserting exit codes and output.
- [ ] Task: Implement execution flow that runs the full pipeline (Parse -> Elaborate -> Infer -> Translate -> IR Eval) for scripts/stdin.
- [ ] Task: Conductor - User Manual Verification 'Phase 2: Script and Stdin Execution' (Protocol in workflow.md)

## Phase 3: Interactive Mode and Error Handling
- [ ] Task: Implement `-i` / `--interactive` flag logic to transition to the REPL after script execution.
- [ ] Task: Enhance error reporting in `Main.lean` to capture and print errors to `stderr` with highlighting, then exit with code 1.
- [ ] Task: Write Tests: Verify error exit codes and stderr output for malformed scripts.
- [ ] Task: Conductor - User Manual Verification 'Phase 3: Interactive Mode and Error Handling' (Protocol in workflow.md)

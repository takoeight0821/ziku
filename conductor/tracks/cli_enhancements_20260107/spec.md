# Specification: CLI Enhancements - Help and Script Execution

## Overview
Enhance the Ziku CLI to support standard command-line interactions, including a help menu, the ability to execute Ziku source files, and support for reading from standard input.

## Goals
- **Usability:** Provide a clear help menu to guide users.
- **Versatility:** Enable non-interactive execution of Ziku programs.
- **Integration:** Support Unix-style piping and redirection via stdin.

## Functional Requirements
1.  **Help Menu:**
    *   Implement `-h` and `--help` flags.
    *   Display usage instructions: `ziku [options] [file]`.
    *   List and describe available options.
2.  **Script Execution:**
    *   If a file path is provided as a positional argument, Ziku should read and execute the file.
    *   The process should exit after execution unless the `-i` or `--interactive` flag is provided.
3.  **Standard Input Support:**
    *   If no file is provided and stdin is not a TTY (or an explicit flag is used), Ziku should read and execute from stdin.
4.  **Interactive Mode:**
    *   Add `-i` / `--interactive` flag to enter the REPL after executing a script or stdin.
5.  **Error Reporting:**
    *   Output parse, type, translation, and evaluation errors to `stderr`.
    *   Include source position and snippet highlighting for errors.
    *   Exit with a non-zero status code on failure.

## Non-Functional Requirements
- **Performance:** Command-line argument parsing should be efficient and not delay REPL startup.

## Acceptance Criteria
- [ ] `lake exe ziku --help` displays usage info.
- [ ] `lake exe ziku script.ziku` executes the script and exits.
- [ ] `echo "1 + 2" | lake exe ziku` executes the piped code and exits.
- [ ] `lake exe ziku script.ziku -i` executes the script and enters the REPL.
- [ ] Errors during script execution result in a non-zero exit code.

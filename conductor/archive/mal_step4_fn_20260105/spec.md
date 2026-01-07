# Specification: MAL Phase 4 - Functions and Control Flow

## Overview
Implement Step 4 of the MAL (Make A Lisp) implementation in Ziku. This phase introduces first-class functions (closures), sequential execution, and conditional logic. It also involves refactoring how built-in operators are handled to support higher-order functions.

## Functional Requirements
- **New Value Types**:
    - `MClosure(params, body, env)`: Represents a user-defined function with captured lexical environment.
    - `MNative(name)`: Represents a built-in native function.
- **Control Flow Special Forms**:
    - `(if test then else)`: Evaluate `test`; if true (not `nil` or `false`), evaluate and return `then`, otherwise evaluate `else`.
    - `(do ...forms)`: Evaluate all forms sequentially and return the result of the last form.
- **Functions (`fn*`)**:
    - `(fn* [params] body)`: Create an `MClosure`.
- **Environment & Application**:
    - Populate the initial global environment with native functions (e.g., `+`, `-`, `*`, `/`, `list`, `count`, `empty?`).
    - **Function Application**: Evaluate the operator and arguments. If the operator is an `MClosure`, bind arguments to parameters in a new environment extending the captured one. If it is `MNative`, execute the corresponding Ziku logic.
- **Lexical Scoping**: Ensure closures correctly capture the environment they were defined in.

## Acceptance Criteria
- A new test file `tests/golden/ir-eval/success/mal_step4_fn.ziku` is created.
- `(if true 1 2)` returns `1`.
- `(if false 1 2)` returns `2`.
- `(do (def! a 1) (+ a 1))` returns `2`.
- `((fn* [a b] (+ a b)) 3 4)` returns `7`.
- Higher-order function usage: `(def! add (fn* [a b] (+ a b))) (add 1 2)` returns `3`.

## Out of Scope
- Tail-Call Optimization (Phase 5).
- Macros (Phase 8).
- Exception handling (Phase 9).

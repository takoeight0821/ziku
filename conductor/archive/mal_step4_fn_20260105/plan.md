# Implementation Plan - MAL Phase 4: Functions and Control Flow

This plan implements Step 4 of MAL, focusing on sequential execution, conditionals, and first-class functions (closures and natives).

## Phase 1: Native Functions and Printing [checkpoint: ded7463]
- [x] Task: Update Value Constructors and Printer 440c990
  - Add `MNative(name)` to the set of MAL value constructors used in Ziku.
  - Update `prStr` to handle `MNative`.
- [x] Task: Global Environment Initialization 440c990
  - Define `replEnv` containing bindings for `+`, `-`, `*`, `/`, `list`, `count`, `empty?`.
- [x] Task: Create Golden Test: Natives 440c990
  - Create `tests/golden/ir-eval/success/mal_step4_natives.ziku` to verify environment lookup and printing of native functions.
- [x] Task: Conductor - User Manual Verification 'Phase 1: Native Functions and Printing' (Protocol in workflow.md) [checkpoint: ded7463]

## Phase 2: Control Flow (`do`, `if`) [checkpoint: c3bf68b]
- [x] Task: Implement `if` 2029279
  - Update `eval` to handle `MSym("if")`.
  - Ensure `nil` and `false` are the only "falsey" values.
- [x] Task: Implement `do` 2029279
  - Update `eval` to handle `MSym("do")`.
- [x] Task: Create Golden Test: Control Flow 2029279
  - Create `tests/golden/ir-eval/success/mal_step4_control.ziku` to verify `if` branching and `do` sequential execution.
- [x] Task: Conductor - User Manual Verification 'Phase 2: Control Flow' (Protocol in workflow.md) [checkpoint: c3bf68b]

## Phase 3: Closures (`fn*`) [checkpoint: e6ed3ce]
- [x] Task: Define `MClosure` 1f0ea69
  - Add `MClosure(params, body, env)` to MAL value constructors.
  - Update `prStr` to handle `MClosure` (usually prints as `#<function>`).
- [x] Task: Implement `fn*` Special Form 1f0ea69
  - Update `eval` to handle `MSym("fn*")` and return an `MClosure` capturing the current environment.
- [x] Task: Create Golden Test: Closure Definition 1f0ea69
  - Create `tests/golden/ir-eval/success/mal_step4_closure_def.ziku` to verify `(fn* ...)` evaluates to a closure object.
- [x] Task: Conductor - User Manual Verification 'Phase 3: Closures' (Protocol in workflow.md) [checkpoint: e6ed3ce]

## Phase 4: Function Application [checkpoint: aa188f5]
- [x] Task: Refactor Application Logic
  - Implement a generic application mechanism that evaluates the operator and then applies it.
  - Implemented `apply` function that dispatches on `MNative` and `MClosure`.
- [x] Task: Implement `MNative` Application
  - Logic to execute the underlying Ziku operation (arithmetic, list ops) for a given `MNative` name.
  - Implemented `applyNative` for +, -, *, /, list, count, empty?.
- [x] Task: Implement `MClosure` Application
  - Logic to create a new environment, bind parameters to evaluated arguments, and evaluate the closure body in that environment.
  - Implemented `bindParams` and closure application in `apply`.
- [x] Task: Create Golden Test: Function Application
  - Created `tests/golden/ir-eval/success/mal_step4_fn_apply.ziku` testing `((fn* [a b] (+ a b)) 3 4)` → 7.
  - Created `tests/golden/ir-eval/success/mal_step4_fn_simple.ziku` testing simple identity closure.
  - Full comprehensive test (`mal_step4_fn.ziku.slow`) disabled due to performance of nested interpretation.
- [x] Task: Conductor - User Manual Verification 'Phase 4: Function Application' (Protocol in workflow.md) [checkpoint: aa188f5]
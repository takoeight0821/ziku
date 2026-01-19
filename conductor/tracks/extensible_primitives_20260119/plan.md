# Implementation Plan: Extensible Primitive Mechanism

This plan outlines the steps to implement a mechanism for defining and using external primitives in Ziku, supporting the Scheme backend with runtime type contracts.

## Phase 1: AST and Parser Updates
Support the `@("backend", "name")` syntax for external declarations.

- [x] Task: Update `Ziku/Syntax.lean` to store external metadata in declarations. [1c47f1a]
    - *Note: Will refine `ExternInfo` to support multiple backends in the next task.*
- [x] Task: Update `Ziku/Syntax.lean` and `Ziku/Parser.lean` for new syntax. [ad95eca]
    - [x] Modify `ExternInfo` in `Ziku/Syntax.lean` to be `List (String × String)` to support multiple backends.
    - [x] Update `Ziku/Parser.lean` to parse `@("backend", "name")` on the RHS of declarations.
    - [x] Support the `|` separator for multiple backends.
    - [x] Ensure `data` declarations can also use this syntax.
- [ ] Task: Conductor - User Manual Verification 'Phase 1: AST and Parser Updates' (Protocol in workflow.md)

## Phase 2: Type Inference for Externals
Integrate external declarations into the Hindley-Milner type inference system.

- [ ] Task: Update `Ziku/Infer.lean` to handle external declarations.
    - [ ] Add external function signatures to the type environment.
    - [ ] Handle opaque data types (external data with no constructors) during type checking.
    - [ ] Ensure opaque types cannot be pattern-matched in Ziku code.
- [ ] Task: Conductor - User Manual Verification 'Phase 2: Type Inference for Externals' (Protocol in workflow.md)

## Phase 3: IR and Translation
Extend the IR and translation pass to handle external calls.

- [ ] Task: Update `Ziku/IR/Syntax.lean` to include an `externalCall` statement.
    - [ ] Add `Statement.externalCall` that stores the external info (for the chosen backend), arguments, and continuation.
- [ ] Task: Update `Ziku/Translate.lean` to translate external function calls to `Statement.externalCall`.
    - [ ] Modify the translation logic to look up the correct backend implementation from the `ExternInfo` list.
- [ ] Task: Conductor - User Manual Verification 'Phase 3: IR and Translation' (Protocol in workflow.md)

## Phase 4: Scheme Backend and Runtime Contracts
Implement code generation for external calls and safety checks at the Ziku-Scheme boundary.

- [ ] Task: Update `Ziku/Backend/Scheme.lean` to generate code for `Statement.externalCall`.
- [ ] Task: Implement Runtime Contracts in the Scheme backend.
    - [ ] Generate Scheme wrappers that verify the types of values returned from external primitives against the declared Ziku types.
- [ ] Task: Conductor - User Manual Verification 'Phase 4: Scheme Backend and Runtime Contracts' (Protocol in workflow.md)

## Phase 5: Refactoring and Final Verification
Migrate existing built-ins to the new mechanism and ensure overall system integrity.

- [ ] Task: Refactor hardcoded built-ins (e.g., `strLen`, `println`) to use the `@extern` mechanism in a core library.
- [ ] Task: Create comprehensive golden tests for:
    - [ ] External function calls.
    - [ ] External constants.
    - [ ] Opaque types and their usage.
    - [ ] Runtime contract violations (ensure they fail gracefully).
- [ ] Task: Conductor - User Manual Verification 'Phase 5: Refactoring and Final Verification' (Protocol in workflow.md)
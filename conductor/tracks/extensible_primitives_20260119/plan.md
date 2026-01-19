# Implementation Plan: Extensible Primitive Mechanism

This plan outlines the steps to implement a mechanism for defining and using external primitives in Ziku, supporting the Scheme backend with runtime type contracts.

## Phase 1: AST and Parser Updates
Support the `@extern` attribute and external declarations in the surface language.

- [x] Task: Update `Ziku/Syntax.lean` to store external metadata in declarations. [1c47f1a]
    - [ ] Define `ExternInfo` structure: `{ platform : String, name : String }`.
    - [ ] Update `Decl.def_`, `Decl.defPat`, and `Decl.data` to include `Option ExternInfo`.
    - [ ] Modify `Decl.def_` to allow an optional body (null for externals).
- [ ] Task: Update `Ziku/Parser.lean` to parse the `@extern` attribute.
    - [ ] Implement a parser for `@extern("platform", "name")`.
    - [ ] Update `parseDecl` to check for attributes before parsing specific declaration types.
    - [ ] Update `parseDefDecl` to handle `def` without a body when `@extern` is present.
    - [ ] Update `parseDataDecl` to allow empty constructor lists when `@extern` is present.
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
    - [ ] Add `Statement.externalCall` that stores the external info, arguments, and continuation.
- [ ] Task: Update `Ziku/Translate.lean` to translate external function calls to `Statement.externalCall`.
    - [ ] Modify the translation logic to recognize calls to identifiers declared as `@extern`.
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

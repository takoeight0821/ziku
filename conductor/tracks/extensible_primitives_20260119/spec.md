# Specification: Extensible Primitive Mechanism

## Overview
This track introduces a mechanism to define and use external primitives (specifically for the Scheme backend) directly from Ziku source files. This allows for a modular standard library and easier integration with host environment features without modifying the compiler's core logic for every new operation.

## Functional Requirements
- **Surface Syntax**:
  - Use a "value-like" syntax for external definitions on the right-hand side of declarations.
  - Syntax: `def name : type = @("backend", "symbol")`
  - Support multiple backends via the `|` separator:
    `def name : type = @("scheme", "scm_name") | @("c", "c_name")`
- **External Definitions**:
  - **Functions**: `def strLen : String -> Int = @("scheme", "string-length")`
  - **Constants**: `def pi : Float = @("scheme", "pi")`
  - **Opaque Types**: `data Vector a = @("scheme", "vector")`
- **Runtime Contracts**: The compiler must generate "boundary glue" in the Scheme backend.
  - When calling a Scheme function from Ziku, the glue code verifies that the returned Scheme value matches the declared Ziku type.
  - When Ziku passes a value to Scheme, the glue ensures it meets any host-level expectations.
- **Type Inference**: External declarations must participate in standard Hindley-Milner type inference like regular Ziku definitions.

## Non-Functional Requirements
- **Extensibility**: Adding a new primitive should only require a Ziku source change.
- **Safety**: Prevent Ziku runtime crashes caused by type mismatches at the `extern` boundary by failing gracefully with a contract error.

## Acceptance Criteria
- [ ] Users can declare an external function using the `@("backend", "name")` syntax.
- [ ] Users can provide implementations for multiple backends using `|`.
- [ ] The compiler successfully translates these declarations into Scheme calls when the Scheme backend is selected.
- [ ] Passing a value of the wrong type to an external primitive results in a runtime contract error.

## Out of Scope
- Supporting backends other than Scheme (for now, but the syntax must support it).
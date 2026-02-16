# Specification - First Class Covalues

## Overview
This track introduces "First Class Covalues" to the Ziku surface language. While the underlying IR (sequent calculus) natively supports duality and continuations, the surface language currently treats labels/goto as second-class control flow constructs. This feature enables passing consumers (continuations) as function arguments, allowing for more expressive control flow patterns directly in Ziku code.

## Functional Requirements

### 1. Surface Syntax Extensions
- **Parameter Definition**: Support a `~` marker for covalue parameters in lambda abstractions and function definitions.
  - Example: `\x ~k => ...`
- **Function Application**: Support passing covalues as arguments using the `~` marker.
  - Example: `f(10, ~some_label)`
- **Covalue Invocation**: The existing `goto(value, k)` syntax must be updated to work with these first-class covalue variables.

### 2. Type System Support
- Introduce a new type constructor for consumers, denoted as `~T`, representing a consumer that expects a value of type `T`.
- Type inference must be updated to:
  - Assign `~T` to parameters marked with `~`.
  - Verify that arguments passed with `~` are valid consumers.
  - Ensure `goto(v, k)` is type-consistent (type of `v` must match the type expected by consumer `k`).

### 3. Translation to IR
- Update the translation layer to map surface covalue parameters to IR constructs.
- A covalue parameter `~k` will likely translate to a name bound in a `mu` or `cocase` at the IR level, allowing it to be used as a `Consumer` in `cut` or `call` statements.

## Acceptance Criteria
- [ ] Ziku parser correctly handles `~` markers in parameters and arguments.
- [ ] Type inference correctly identifies and validates `~T` types.
- [ ] A function defined as `let f = \x ~k => goto(x + 1, k)` can be successfully compiled.
- [ ] Passing a label to such a function works: `label exit { f(10, ~exit) }` evaluates to `11`.
- [ ] Passing a "returned" or "passed-through" covalue works as expected.

## Out of Scope
- Storing covalues in data structures (moved to issue `issues/2026-01-05-covalues-in-data-structures.md`).
- First-class covalues that take multiple arguments (moved to issue `issues/2026-01-05-multi-argument-covalues.md`).

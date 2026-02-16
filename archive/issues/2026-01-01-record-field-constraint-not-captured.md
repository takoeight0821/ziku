---
date: 2026-01-01
title: Record field access constraints not captured in polymorphic functions
status: resolved
resolved_date: 2026-01-01
---

# Record field access constraints not captured in polymorphic functions

## Description

When type-inferring a polymorphic function that accesses a record field, the constraint that the argument must be a record with that field is not captured in the inferred type.

## Example

```ziku
\r => r .x
```

**Current behavior**: Inferred type is `(_t0 -> _t1)`

**Expected behavior**: The type should express that `_t0` must be a record containing field `x` of type `_t1`, such as:
- `{ x : _t1, ... } -> _t1` (row polymorphism)
- Or a type class constraint like `HasField "x" _t0 _t1 => _t0 -> _t1`

## Impact

This limitation means that:
1. The type system accepts code that may fail at runtime
2. Type errors for invalid field access are only caught when the function is applied to a concrete record type
3. The inferred type doesn't document the function's requirements

## Context

- File: `Ziku/Infer.lean`
- The `fieldAccess` constraint in `genConstraints` defers field lookup to the constraint solver
- When the record type is a type variable, `tryResolveFieldAccess` skips it (returns `false`)
- This causes the constraint to remain unresolved, leaving the type variables unconstrained

```lean
| .var _ _ =>
    -- Record type not yet resolved, skip for now
    .ok (state, false)
```

## Possible Solutions

1. **Row polymorphism**: Extend the type system to support row types like `{ x : Int | r }` where `r` represents the rest of the record
2. **Type class constraints**: Add a `HasField` constraint that can be solved during type checking
3. **Deferred constraints**: Keep unresolved field constraints and report them as errors if they remain unresolved after inference completes

## Related Tests

- `tests/golden/infer/success/record_polymorphic_access.ziku` - demonstrates the current behavior
- `tests/golden/infer/success/record_function_param.ziku` - works correctly when concrete type is provided

## Resolution

Implemented **row polymorphism** as described in `docs/research/ziku-type-inference-design.md`.

### Changes Made

1. **Extended `Ty.record`** in `Ziku/Syntax.lean`:
   - Changed from `record : SourcePos → List (Ident × Ty) → Ty`
   - To `record : SourcePos → List (Ident × Ty) → Option Ty → Ty`
   - The optional `Ty` is the row tail (e.g., `{ x : Int | ρ }` where ρ is a row variable)

2. **Updated type utilities** in `Ziku/Type.lean`:
   - `Ty.applySubst` - applies substitution to row tail
   - `Ty.freeVars` - extracts free variables from row tail

3. **Updated type inference** in `Ziku/Infer.lean`:
   - Field access now generates: `unify(recTy, { field : resultTy | rowVar })`
   - Implemented row unification algorithm with four cases:
     - Both closed: fields must match exactly
     - Left open, right closed: unify left tail with right's extra fields
     - Left closed, right open: unify right tail with left's extra fields
     - Both open: create fresh row variable for both tails
   - Removed the old `fieldAccess` constraint system

### Result

```ziku
\r => r .x
```

Now infers type: `({ x : _t1 | _t2 } -> _t1)`

Where `_t2` is a row variable representing any additional fields the record may have.

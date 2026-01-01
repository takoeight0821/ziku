---
date: 2026-01-01
title: Record field access constraints not captured in polymorphic functions
status: open
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

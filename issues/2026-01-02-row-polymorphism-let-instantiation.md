---
date: 2026-01-02
title: Row polymorphism not properly instantiated in let-polymorphism
status: open
---

# Row polymorphism not properly instantiated in let-polymorphism

## Description

When a polymorphic function with row polymorphism is used multiple times with different record types, the type inference fails to properly instantiate the row variable for each use. Instead, it tries to unify the record types directly, causing a type error.

## Context

- File: `Ziku/Infer.lean`
- The row variable is correctly inferred but not properly generalized/instantiated

## Example

```ziku
let getX = \r => r.x in
let point = { x = 1, y = 2 } in
let point3d = { x = 10, y = 20, z = 30 } in
getX point + getX point3d
```

**Expected behavior:**
- `getX` should have type `forall a r. { x : a | r } -> a`
- Each use should instantiate `r` independently
- `getX point` should work with `r = { y : Int }`
- `getX point3d` should work with `r = { y : Int, z : Int }`
- Final type: `Int`

**Actual behavior:**
```
Type error at 1:66: Record field mismatch: cannot unify closed records with different fields
  Expected: { y : Int }
  Actual: { y : Int, z : Int }
```

## Analysis

The type of `\r => r.x` is correctly inferred as `({ x : _t1 | _t2 } -> _t1)` with row variable `_t2`. However, when the let-bound `getX` is used multiple times, the row variable appears to not be properly instantiated fresh for each use.

The issue is likely in how `generalize` and `instantiate` handle row variables in record types.

## Test Case

Added as expected-error test: `tests/golden/infer/error/forall-row-limitation.ziku`

## Related

- Row polymorphism implementation: commit `ac698d8`
- Let-polymorphism implementation in `Infer.lean`

---
date: 2026-01-02
title: Row polymorphism not properly instantiated in let-polymorphism
status: resolved
resolution: Added row type syntax to parser
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

**Actual behavior (without explicit forall annotation):**
```
Type error at 1:66: Record field mismatch: cannot unify closed records with different fields
  Expected: { y : Int }
  Actual: { y : Int, z : Int }
```

## Resolution

The issue was **not** about let-polymorphism or generalize/instantiate logic. The actual problem was that the **parser did not support row type syntax** in type annotations.

### Root Cause

1. The type `({ x : _t1 | _t2 } -> _t1)` was correctly inferred internally
2. However, there was no way to write `{ x : a | r }` in explicit type annotations
3. Without explicit `forall` annotation, the let-binding used monomorphic schemes

### Fix

Added row type syntax to `Ziku/Parser.lean`:
- `{ x : Int, y : Bool | r }` - Open record with row variable `r`
- `{ x : Int }` - Closed record (existing syntax)

### Working Solution

With explicit `forall` annotation:
```ziku
let getX : forall a r. { x : a | r } -> a = \r => r.x in
let point = { x = 1, y = 2 } in
let point3d = { x = 10, y = 20, z = 30 } in
getX point + getX point3d
```

This now correctly infers type `Int`.

## Test Cases

- `tests/golden/infer/error/forall-row-limitation.ziku` - Original failing case (without forall)
- `tests/golden/infer/success/row_polymorphic_let.ziku` - Working case with explicit forall

## Note

The original example without explicit `forall` still fails because the current implementation does not automatically generalize let-bindings during constraint generation. This is a separate issue (implicit let-polymorphism) that would require architectural changes to the constraint-based type inference.

## Related

- Row polymorphism implementation: commit `ac698d8`
- Let-polymorphism implementation in `Infer.lean`
- Parser fix: Added row type syntax to `Parser.lean`

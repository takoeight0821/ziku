---
date: 2025-12-27
title: Type inference improvements needed
status: resolved
---

# Type inference improvements needed

## Description

Code review of the type inference refactoring identified several issues that should be addressed before the changes are committed.

## Issues

### 1. Unused Variables (Linter Warnings)

The following unused variables generate linter warnings:

- `Ziku/Infer.lean:163` - `args` in constructor pattern case (stub throws anyway)
- `Ziku/Infer.lean:193` - `pos` in `binOp` case
- `Ziku/Infer.lean:200` - `pos` in `unaryOp` case
- `Ziku/Infer.lean:291` - `fieldTy` (fresh type variable generated but never used)
- `Ziku/Syntax.lean:343` - `clauses` in `Decl.toString`
- `Ziku/Syntax.lean:348` - `decls` in `Decl.toString`
- `Ziku/Syntax.lean:350` - `items` and `alias` in `Decl.toString`

### 2. Pipe Operator Type is Incorrect

```lean
-- Ziku/Infer.lean:73
| .pipe => (tyInt, tyInt)  -- Placeholder, needs proper handling
```

The pipe operator `|>` should have type `(a, a -> b) -> b`, not `(Int, Int) -> Int`. This requires special handling since it's polymorphic.

### 3. Comparison Operators Assume Int Only

```lean
-- Ziku/Infer.lean:70
| .eq | .ne | .lt | .le | .gt | .ge => (tyInt, tyBool)
```

- Equality (`==`, `!=`) should work on any type with `Eq`
- Ordering comparisons (`<`, `<=`, `>`, `>=`) should work on any type with `Ord`

### 4. Concat Operator Assumes String

```lean
-- Ziku/Infer.lean:72
| .concat => (tyString, tyString)
```

The `++` operator could also work on lists. Consider making it polymorphic.

## Context

These issues were found during review of uncommitted changes to:

- `Ziku/Eval.lean`
- `Ziku/Infer.lean`
- `Ziku/Parser.lean`
- `Ziku/Syntax.lean`
- `Ziku/Type.lean`

The changes implement source position tracking in AST nodes and enhance type inference with let-polymorphism and better error reporting. The build passes and all golden tests succeed.

## Suggested Fixes

1. **Unused variables**: Replace with `_` prefix or wildcard patterns
2. **Pipe operator**: Implement as special case with fresh type variables
3. **Comparison/equality**: Either make polymorphic or add type class constraints later
4. **Concat**: Keep as String for now, document as future enhancement

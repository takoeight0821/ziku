---
date: 2025-12-28
title: Parser bugs with hash self-reference and callable codata
status: resolved
---

# Parser bugs with hash self-reference and callable codata

## Description

Two parser issues were discovered during golden test updates. Both have been resolved.

## Issue 1: Hash Self-Reference in Codata [RESOLVED]

**File**: `tests/golden/parser/hash.ziku`
**Input**:
```
{ #.head => 1, #.tail => # }
```

**Status**: Fixed

**Resolution**:
- Added `hash` constructor to `Expr` type in `Syntax.lean`
- Updated parser to allow `#` as an expression (returns `Expr.hash`)
- Added special handling in `parseAppArgs` to not consume `#.field` or `#(arg)` as application arguments (to avoid ambiguity with new codata clauses)
- Added `hash` case to `Eval.lean`, `Infer.lean`, and `Elaborate.lean`
- Re-enabled `parser/hash` test

## Issue 2: Callable Codata with Field Access [RESOLVED]

**File**: `tests/golden/eval/codataNested.ziku`
**Input**:
```
{
  #(x).value => x * 2
}(10).value
```

**Status**: Fixed

**Resolution**:
- Modified `parseAppArgs` to call `parseFieldRest` after processing parenthesized application arguments
- This allows `f(1).x` to be parsed as field access `.x` on the result of `f(1)`
- Applied same fix to `parseAppArgsStop` for consistency
- Re-enabled `eval/codataNested` test

## Test Status

All 121 tests now pass.

## Summary of Changes

### Syntax.lean
- Added `hash : SourcePos → Expr` constructor
- Updated `Expr.pos`, `Expr.exprSize`, `Expr.freeVars`, `Expr.toString` for hash

### Parser.lean
- Changed `parseAtomExpr` and `parseAtomExprStop` to return `Expr.hash` for `#`
- Added check in `parseAppArgs`/`parseAppArgsStop` to not consume `#.field` or `#(arg)` as application arguments
- Added call to `parseFieldRest`/`parseFieldRestStop` after parenthesized application to enable `f(1).x`

### Eval.lean
- Added `hash` case (returns `none`)

### Infer.lean
- Added `hash` case (throws "not implemented")

### Elaborate.lean
- Added explicit `hash` case in `elaborateAll`

### GoldenTest.lean
- Re-enabled `parser/hash` test
- Re-enabled `eval/codataNested` test

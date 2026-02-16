---
date: 2026-01-03
title: Nested constructor patterns not supported in translation
status: resolved
resolved: 2026-01-03
---

# Nested constructor patterns not supported in translation

## Description

The translation phase does not support nested constructor patterns in match expressions. Patterns like `Cons(MNum(a), rest)` where constructor arguments contain other constructors fail with "Translation not implemented for nested constructor pattern".

## Context

- File: `Ziku/Translate.lean:155`
- Function: `extractVarFromPat` throws error on `.con` patterns

**Current limitation:**
```ziku
-- This fails:
match args {
| Cons(MNum(a), Cons(MNum(b), MNil)) => a + b
| _ => 0
}

-- Must be written as nested matches:
match args {
| Cons(h1, t1) =>
  match h1 {
  | MNum(a) =>
    match t1 {
    | Cons(h2, t2) =>
      match h2 {
      | MNum(b) =>
        match t2 {
        | MNil => a + b
        | _ => 0
        }
      | _ => 0
      }
    | _ => 0
    }
  | _ => 0
  }
| _ => 0
}
```

## Proposed Solution

Implement pattern compilation that transforms nested patterns into nested case expressions:

```
match x { | Cons(MNum(a), rest) => body }
```
compiles to:
```
match x {
| Cons(tmp1, rest) =>
  match tmp1 {
  | MNum(a) => body
  | _ => <fail>
  }
}
```

Key changes needed:
1. Modify `patternToIRBranch` to handle nested patterns
2. Generate fresh variables for nested constructor arguments
3. Wrap body in nested case expressions for each nested pattern
4. Handle failure cases (fall through to next branch or wildcard)

## Impact

This is blocking MAL implementation which uses patterns like:
- `Cons(MStr(tok), MStr(rest))` in tokenizer
- `Cons(MNum(a), Cons(MNum(b), MNil))` in arithmetic application

## Related

- `Ziku/Translate.lean:142-156` - `extractVarFromPat` function
- `tests/golden/ir-eval/success/mal_step3_eval.ziku` - blocked test file

## Resolution

Implemented pattern compilation with join points for failure handling:

1. Added `ArgPattern` type to categorize constructor argument patterns
2. Implemented `compilePattern` to compile patterns with success/failure continuations
3. Implemented `compileCases` to chain match branches with failure fallthrough
4. Updated `translateExpr` for `match_` to use new compilation

Nested patterns are now flattened into nested case expressions with `mu`/`covar` for failure jumps.

New tests added:
- `match_nested_simple.ziku` - Basic nested pattern
- `match_nested_with_fallback.ziku` - Nested with fallback
- `match_nested_literal.ziku` - Literal in nested position
- `match_multi_nested.ziku` - Multiple nesting levels

---
date: 2026-01-02
title: IR evaluator limitations for string/rune operations
status: closed
---

# IR evaluator limitations for string/rune operations

## Description

During MAL Phase 2 implementation, several limitations were discovered in the IR evaluator that prevent certain operations from working correctly.

## Issues Found

### 1. String equality comparison not supported - FIXED

The `==` operator now works for String comparison in the IR evaluator.

```ziku
// This now works
if tok == "nil" then MNil else MSym(tok)
```

**Fix:** Added `==` and `!=` pattern matches for String literals in `evalBinOp` (`Ziku/IR/Eval.lean`).

### 2. Rune equality comparison not supported - FIXED

The `==` operator now works for Rune comparison in the IR evaluator.

```ziku
// This now works
if c == '(' then true else false
```

**Fix:** Added pattern match for Char literals in `evalBinOp` (`Ziku/IR/Eval.lean`).

### 3. Lazy evaluation issue with complex recursion - FIXED

When combining tokenizer output with parser in a full `read` function, the IR evaluator was getting stuck. The second element of Cons cells appeared as suspended computation `(μ_α166. ⟨(fix tokenize...` instead of being evaluated.

```ziku
// This now works
let read = \s =>
  let tokens = tokenize s in
  match readForm tokens { ... }
```

**Fix:** Implemented static focusing transformation (`5082ed5`) that converts lazy data constructors to eager evaluation. The transformation wraps `dataCon` arguments in `let` bindings to force evaluation before construction. This allows pattern matching on recursively-constructed data structures.

See: `Ziku/IR/Syntax.lean` - `focusStatement`, `focusProducer` functions.

### 4. `&&` operator issue in Scheme backend - FIXED

The `&&` operator now generates correct Scheme code.

**Fix:** Changed Scheme backend to use named helper functions (`ziku-and`, `ziku-or`) defined in the runtime instead of inline lambda wrappers (`Ziku/Backend/Scheme.lean`).

## Impact

All issues have been resolved:

- MAL Phase 1 and Phase 2 tests pass in both IR evaluator and Scheme backend
- Full integration of `read` function (tokenize + parse) works correctly
- String/Rune equality works natively
- Focusing transformation enables eager evaluation of recursive data structures

## Test Files

- `tests/golden/ir-eval/success/string_equality.ziku` - tests String `==` and `!=`
- `tests/golden/ir-eval/success/rune_equality.ziku` - tests Rune `==` and `!=`

## Related

- MAL implementation plan: `docs/research/mal.md`
- Phase 2 plan: `.claude/plans/mutable-sparking-babbage.md`

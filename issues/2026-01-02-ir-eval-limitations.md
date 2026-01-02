---
date: 2026-01-02
title: IR evaluator limitations for string/rune operations
status: partially-resolved
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

### 3. Lazy evaluation issue with complex recursion - KNOWN LIMITATION

When combining tokenizer output with parser in a full `read` function, the IR evaluator gets stuck. The second element of Cons cells appears as suspended computation `(μ_α166. ⟨(fix tokenize...` instead of being evaluated.

```ziku
// This fails - tokenize result not fully evaluated when matched
let read = \s =>
  let tokens = tokenize s in
  match readForm tokens { ... }
```

**Status:** This is a fundamental design limitation, not a bug.

**Explanation:** The IR evaluator uses lazy evaluation for data constructors. A `dataCon` (including `Cons` cells) is only considered a "value" when ALL its arguments are values. Recursive calls create μ-abstractions (suspended computations) in tail position, which prevents the entire structure from being a value. Pattern matching on such structures gets stuck because reduction rules require values.

This design enables lazy evaluation and potentially infinite data structures, but means that deeply recursive constructions may not fully evaluate in some contexts.

**Workaround:** Structure code to avoid deeply nested recursive Cons constructions that need to be pattern-matched immediately. Consider using continuation-passing style or explicit forcing where needed.

### 4. `&&` operator issue in Scheme backend - FIXED

The `&&` operator now generates correct Scheme code.

**Fix:** Changed Scheme backend to use named helper functions (`ziku-and`, `ziku-or`) defined in the runtime instead of inline lambda wrappers (`Ziku/Backend/Scheme.lean`).

## Impact

- MAL Phase 2 individual components (tokenizer, parser) work correctly with native `==`
- Full integration of `read` function (tokenize + parse) still fails due to lazy evaluation design
- String/Rune equality now works natively without workarounds

## Test Files

- `tests/golden/ir-eval/success/string_equality.ziku` - tests String `==` and `!=`
- `tests/golden/ir-eval/success/rune_equality.ziku` - tests Rune `==` and `!=`

## Related

- MAL implementation plan: `docs/research/mal.md`
- Phase 2 plan: `.claude/plans/mutable-sparking-babbage.md`

---
date: 2026-01-03
title: IR evaluator gets stuck on complex nested pattern expressions
status: open
---

# IR evaluator gets stuck on complex nested pattern expressions

## Description

The IR evaluator gets stuck (returns `Stuck`) when evaluating complex expressions that involve nested pattern matching on lazily evaluated producers. The Scheme backend handles these same expressions correctly.

## Context

- Discovered while implementing MAL Step 3 (`mal_step3_eval.ziku`)
- The test expression `(let* [a 2 b 3] (+ a (* b 4)))` works via Scheme backend but gets stuck in IR eval
- Similarly, `mal_step2_read.ziku` which parses `(+ 1 (* 2 3))` also gets stuck

**Symptoms:**
- IR eval returns `Stuck: ⟨(Cons (MStr ...) ...) | case { ... }⟩`
- The scrutinee of the case expression contains unevaluated `μ` abstractions
- Scheme backend produces correct output

## Analysis

The issue appears to be that the IR evaluator doesn't fully reduce the scrutinee before attempting pattern matching. When the scrutinee is a `Cons` containing lazy producers (like `(μ_α. runeToStr(...))`) instead of values, the case expression cannot match.

**Example stuck expression (simplified):**
```
⟨(Cons (MStr (μ_α. runeToStr('('; _α))) ...) | case { Cons(_tmp, rest) ⇒ ... }⟩
```

The `MStr` constructor contains an unevaluated `μ_α. runeToStr(...)` instead of an actual string value.

## Workaround

Use the Scheme backend for complex MAL-style programs. The Scheme backend correctly handles these patterns because it uses strict evaluation during code generation.

## Potential Solutions

1. **Eager evaluation of constructor arguments**: When constructing data, force evaluation of arguments to values
2. **Pattern-match driven evaluation**: When matching against a case, recursively evaluate the scrutinee until it becomes a value
3. **WHNF normalization**: Implement weak head normal form reduction before case analysis

## Impact

- MAL implementation tests only pass via Scheme backend
- IR eval golden tests for MAL need alternative approach or skipping
- Does not affect simpler tests that don't involve complex lazy evaluation chains

## Related Files

- `tests/golden/ir-eval/success/mal_step2_read.ziku` - gets stuck
- `tests/golden/ir-eval/success/mal_step3_eval.ziku` - gets stuck
- `Ziku/IR/Eval.lean` - IR evaluator implementation

## Reproduction

```bash
# This gets stuck:
./.lake/build/bin/ziku-test eval tests/golden/ir-eval/success/mal_step3_eval.ziku

# This works:
./.lake/build/bin/ziku-test scheme tests/golden/ir-eval/success/mal_step3_eval.ziku > /tmp/test.ss
scheme --script /tmp/test.ss
# Output: "14"
```

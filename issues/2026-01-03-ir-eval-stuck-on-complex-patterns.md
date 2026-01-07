---
date: 2026-01-03
title: IR evaluator gets stuck on complex nested pattern expressions
status: closed
resolution: Fixed by refactoring IR evaluator to use environment-based evaluation (see track `fix_ir_eval_stuck_20260105`)
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

The issue is **code explosion during substitution-based evaluation**, not focusing or pattern matching semantics.

**Key findings:**
1. **Focusing is correctly implemented** - the `Focusing.lean` module properly lifts μ-abstractions out of dataCon arguments
2. **Simpler tests pass** - `mal_parser_only.ziku`, `mal_eval_only.ziku`, `mal_with_let.ziku` (single binding) all work
3. **Code explosion** - when combining parser + eval, each substitution duplicates large IR code blocks
4. **Fuel exhaustion** - the program exhausts the 100,000 step fuel limit due to exponential code growth

**The pattern that triggers the issue:**
- Complex programs with many recursive functions (parser, tokenizer, eval, etc.)
- Each function application duplicates the entire closure body
- With nested calls, IR term size grows exponentially

**Evidence:**
- `mal_parser_only.ziku` (just parser, no eval) → works, outputs correct AST
- `mal_let_two_bindings.ziku` (eval with manual AST, no parser) → works, outputs 3
- `mal_let_two_simple.ziku` (parser + eval with two bindings) → stuck/timeout
- Translated IR for `mal_let_two_simple.ziku` is ~10KB of text for a simple test

## Workaround

Use the Scheme backend for complex MAL-style programs. The Scheme backend correctly handles these patterns because it uses strict evaluation during code generation.

## Potential Solutions

1. **Graph reduction / sharing**: Instead of textual substitution, use sharing to avoid duplicating code
2. **Environment-based evaluation**: Use closures with environments instead of direct substitution
3. **Increase fuel limit**: Simple workaround but doesn't scale for very complex programs
4. **Use Scheme backend**: The Scheme backend compiles to efficient code without substitution overhead

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

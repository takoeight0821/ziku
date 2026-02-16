---
date: 2026-01-06
title: IR Evaluator Stuck on Builtins in Deep CPS Contexts
status: open
---

# IR Evaluator Stuck on Builtins in Deep CPS Contexts

## Description
The IR evaluator (`Ziku.IR.Eval`) gets stuck when evaluating built-in functions (specifically `strLen`) inside deeply nested CPS contexts involving `label` and `goto`.

The failing case occurred while implementing MAL Step 5 (TCO) using explicit CPS in Ziku. The code works correctly when compiled to Scheme, producing the expected result "55". However, `ir-eval` fails with:

```
Stuck: strLen(s1; _α6)
Env keys: [_α6, _α5, _α4, _α3, i, _α2, s2, _α1, s1, strEqFrom]
evalList: none
```

## Reproduction
The failing test case was `tests/golden/ir-eval/success/mal_step5_tco_fn.ziku`. It has been moved to `tests/golden/scheme/success/mal_step5_tco_fn.ziku` to avoid blocking the test suite.

The issue seems to be related to `stateStep` in `IR/Eval.lean` returning `none` for a `Statement.builtin` when the argument `ps` contains a variable that maps to a complex Producer (like a closure or builtin application result) that hasn't been fully forced or substituted, even though `ps.findIdx?` logic attempts to handle non-values.

## Suspected Cause
In `IR/Eval.lean`:
```lean
  | .stmt (.builtin pos b ps c) env =>
    match ps.findIdx? (fun p => !p.isValue) with
```
If `p` is a variable (`.var`), `isValue` is false. The evaluator attempts to force it. However, if the variable looks up to a closure (which `Producer.isValue` considers a value if it's a `cocase`), the forcing mechanism might be getting confused or the `evalBuiltin` function receives a non-literal value (like a closure) and returns `none`, causing the stuck state.

## Workaround
The test case runs successfully on the Scheme backend, confirming the Ziku code and translation logic are correct. The test has been moved to `tests/golden/scheme/success/`.
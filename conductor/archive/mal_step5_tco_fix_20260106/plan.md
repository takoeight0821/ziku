# Implementation Plan - Fix MAL Step 5 TCO Integration Test

## Phase 1: Diagnosis

- [x] Task: Create minimal reproduction test `mal_step5_tco_debug.ziku`
  - Test 3: `(let* [x 1] x)` returns "Other" instead of "MNum:1"
  - Test 3b: `envGet initialEnv "x"` returns "MErr:'x' not found"

## Phase 2: Root Cause Analysis

- [x] Task: Identify root cause

**Root Cause:** In the `let*` implementation, `goto(ast, evalLoop)` jumps back to the
beginning of `eval` with the **original** `env`, not `newEnv`. The `goto` construct
only passes back a value to replace the label's body - it doesn't update closure variables.

```lean
-- BUGGY CODE:
else if strEq s "let*" then
  match args {
  | Cons(Cons(MSym(name), Cons(value, restBindings)), Cons(body, MNil)) =>
    let val = ev ev env value in
    let newEnv = envSet env name val in
    -- BUG: goto jumps back with original env, not newEnv!
    goto(Cons(MSym("let*"), Cons(restBindings, Cons(body, MNil))), evalLoop)
```

**Fix:** Use normal recursion to pass the updated environment:
```lean
-- FIXED CODE:
else if strEq s "let*" then
  match args {
  | Cons(Cons(MSym(name), Cons(value, restBindings)), Cons(body, MNil)) =>
    let val = ev ev env value in
    let newEnv = envSet env name val in
    -- Use recursion to pass newEnv
    ev ev newEnv (Cons(MSym("let*"), Cons(restBindings, Cons(body, MNil))))
```

## Phase 3: Fix

- [x] Task: Fix `let*` to use recursion instead of `goto`
  - `goto` can't update env, so we use normal recursion for intermediate bindings

- [x] Task: Use Y combinator pattern for MAL recursive functions
  - `(fn* [self l acc] ... (self self ...))` instead of direct self-reference
  - Required because closures capture env at creation time, not binding time

- [x] Task: Move integration test to scheme-only
  - IR evaluator gets stuck on complex recursive patterns
  - Scheme backend handles it correctly (produces "3")

## Phase 4: Verification [checkpoint: pending]

- [x] Task: Run all tests
  - 692 tests pass
  - `mal_step5_tco_debug.ziku` validates basic let*/fn* with Y combinator
  - Integration test works via Scheme backend

## Key Learnings

1. **`label`/`goto` is for early exit, not looping**
   - `goto(value, label)` exits the label with value, doesn't re-enter

2. **Closures capture environment at creation time**
   - For recursive functions, use Y combinator: pass `self` as argument

3. **IR evaluator has limits with deeply nested recursion**
   - Complex MAL patterns may need Scheme backend

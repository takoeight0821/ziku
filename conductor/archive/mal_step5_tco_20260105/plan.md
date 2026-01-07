# Implementation Plan - MAL Phase 5: Tail-Call Optimization

This plan implements Step 5 of MAL. TCO is achieved through:
1. **Scheme backend CPS transformation** - tail calls become jumps
2. **IR evaluator fuel-based execution** - prevents stack overflow
3. **Normal recursion** in surface language - no special syntax needed

## Background: label/goto Semantics

Ziku's `label`/`goto` is for **early exit**, not looping:
- `label name { body }` - creates exit point, body returns normally
- `goto(value, name)` - jumps **out** to label with value (like `return`)

Example: `label loop { goto(42, loop) }` returns `42`, doesn't loop.

For TCO, we rely on the compilation pipeline, not explicit `goto`.

## Phase 1: Basic TCO Infrastructure [checkpoint: b07f354]
- [x] Task: Create `mal_step5_tco_basic.ziku` Golden Test
  - Wrap main `eval` in `label evalLoop { ... }`
  - Test: `(+ 1 2)` evaluates to `3`
- [x] Task: Conductor - User Manual Verification

## Phase 2: Special Forms (`let*`, `do`, `if`)
- [x] Task: Implement `let*`
  - Process bindings sequentially, create child env
  - Recursive eval for body (TCO via backend CPS)
  - Test: `(let* [x 1 y 2] (+ x y))` → `3`
- [x] Task: Implement `do`
  - Evaluate all expressions in sequence
  - Return last expression value
  - Test: `(do 1 2 3)` → `3`
- [x] Task: Implement `if`
  - `nil` and `false` are falsey, everything else truthy
  - Test: `(if true 1 2)` → `1`, `(if nil 1 2)` → `2`
- [x] Task: Conductor - User Manual Verification 'Phase 2: Special Forms'

## Phase 3: Function Application with TCO
- [x] Task: Complete evaluator with closures
  - `fn*` creates closure capturing environment
  - Application binds params, evaluates body
  - TCO happens via backend CPS transformation
- [x] Task: Create Golden Test: Recursive Function
  - Test accumulator-style recursion: `(sum 10 0)` → `55`
  - Demonstrates TCO works (no stack overflow)
- [x] Task: Conductor - User Manual Verification 'Phase 3: Function Application'

## Phase 4: Integration Test
- [x] Task: Create comprehensive TCO test
  - Combine `let*`, `do`, `if`, `fn*` in deep recursion
  - Verify no stack overflow for large inputs
- [x] Task: Conductor - Final Verification

## Implementation Notes

### TCO Architecture

```
Surface Ziku → IR (sequent calculus) → Scheme (CPS)
                                           ↓
                                    Tail calls become
                                    continuation jumps
```

### label/goto Use Cases

Use `label`/`goto` for:
- Early exit from nested computation
- Exception-like error handling
- NOT for TCO looping (backend handles this)

### Completed Test Files

| File | Features |
|------|----------|
| `mal_step5_tco_basic.ziku` | Eval with label infrastructure |
| `mal_step5_tco_let.ziku` | `let*` with sequential bindings |

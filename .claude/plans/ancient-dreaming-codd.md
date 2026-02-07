# MTL-Style Targeted Refactoring: MonadFreshCounter Typeclass

**Date**: 2026-02-08

## Context

Multiple modules in Ziku share an identical pattern: maintain a `Nat` counter in monadic state, increment it, and produce a prefixed fresh name string. This duplicated logic exists in 4 modules with slight variations. Additionally, `GenM` is defined in both `Infer.lean` and `Backend/Scheme.lean` with completely different types, causing potential confusion.

This refactoring extracts the shared pattern into a `MonadFreshCounter` typeclass and resolves the name collision.

## Changes

### 1. Create `Ziku/MonadFresh.lean` (new file)

Define `MonadFreshCounter` typeclass with a default instance for `MonadState Nat m`:

```lean
class MonadFreshCounter (m : Type → Type) where
  nextCounter : m Nat

instance [MonadState Nat m] : MonadFreshCounter m where
  nextCounter := do
    let n ← get; set (n + 1); pure n

def freshName [Monad m] [MonadFreshCounter m] (prefix : String) : m String := do
  let n ← MonadFreshCounter.nextCounter
  pure s!"{prefix}{n}"
```

Add to `lakefile.lean` lean_lib sources.

### 2. Refactor `Ziku/IR/Focusing.lean`

- Import `Ziku.MonadFresh`
- Delete local `freshVar` (lines 36-39) — the default instance covers `FocusM = StateT Nat Id`
- Replace `freshVar` calls with `freshName "_f"` at all call sites (~4 locations)

### 3. Refactor `Ziku/Backend/Scheme.lean`

- Import `Ziku.MonadFresh`
- Rename `GenM` → `SchemeGenM` (line 134 + all ~30 occurrences)
- Simplify `freshVar` to delegate to `freshName`:
  ```lean
  def freshVar (pfx : String := "g") : SchemeGenM String :=
    freshName s!"%{pfx}"
  ```
  Keep `freshVar` as a wrapper since call sites pass varying prefixes (`"fn"`, `"v"`, `"arg{i}"`, etc.)

### 4. Refactor `Ziku/Translate.lean`

- Import `Ziku.MonadFresh`
- Add custom `MonadFreshCounter TranslateM` instance (accesses `freshCounter` field from `TranslateState`):
  ```lean
  instance : MonadFreshCounter TranslateM where
    nextCounter := do
      let s ← get
      let n := s.freshCounter
      set { s with freshCounter := n + 1 }
      pure n
  ```
- Simplify `freshCovar` and `freshVar`:
  ```lean
  def freshCovar : TranslateM Ident := freshName "_α"
  def freshVar : TranslateM Ident := freshName "_tmp"
  ```

### 5. Leave `Ziku/Infer.lean` unchanged

`freshTyVar` has level-tracking side effects (records `varLevels`) beyond simple counter increment. Forcing it through `MonadFreshCounter` would lose clarity without practical gain.

## Files to Modify

| File | Action |
|------|--------|
| `Ziku/MonadFresh.lean` | **Create** — typeclass + default instance + `freshName` helper |
| `lakefile.lean` | Add `MonadFresh` to sources |
| `Ziku/IR/Focusing.lean` | Import, delete `freshVar`, use `freshName "_f"` |
| `Ziku/Backend/Scheme.lean` | Import, rename `GenM`→`SchemeGenM`, simplify `freshVar` |
| `Ziku/Translate.lean` | Import, add instance, simplify `freshCovar`/`freshVar` |

## Key Constraint

Fresh name prefixes must be preserved exactly (`_f`, `_α`, `_tmp`, `%g`, `%fn`, `%v`, etc.) — any change would break golden tests.

## Verification

1. `mise run docker:build-check` — build succeeds
2. `mise run docker:test` — all golden tests pass with zero changes to `.golden` files
3. Specifically watch: `ir-eval` (Focusing), `emit-scheme`/`scheme-only` (Scheme), `emit-translate` (Translate)

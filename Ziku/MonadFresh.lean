/-!
# MonadFreshCounter Typeclass

Provides a shared abstraction for generating fresh names from a `Nat` counter.
Multiple modules (Focusing, Scheme backend, Translate) share this pattern.
-/

/-- Typeclass for monads that can produce a fresh `Nat` counter value. -/
class MonadFreshCounter (m : Type → Type) where
  /-- Get the next counter value, incrementing the internal state. -/
  nextCounter : m Nat

instance [Monad m] [MonadStateOf Nat m] : MonadFreshCounter m where
  nextCounter := do
    let n ← MonadStateOf.get
    MonadStateOf.set (n + 1)
    pure n

/-- Generate a fresh name by combining a prefix with the next counter value. -/
def freshName [Monad m] [MonadFreshCounter m] (pfx : String) : m String := do
  let n ← MonadFreshCounter.nextCounter
  pure s!"{pfx}{n}"

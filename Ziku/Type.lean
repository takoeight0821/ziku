namespace Ziku

inductive Ty where
  | int
  | var : Nat → Ty
  deriving Repr, BEq

abbrev Subst := List (Nat × Ty)

end Ziku

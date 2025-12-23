import Ziku.Syntax

namespace Ziku

/-!
# Type System

This module provides type inference utilities, using the `Ty` type from Syntax.lean.
-/

-- Type substitution
abbrev Subst := List (Ident × Ty)

-- Apply substitution to a type
partial def Ty.applySubst (subst : Subst) : Ty → Ty
  | .var x => match subst.lookup x with
    | some ty => ty.applySubst subst  -- Apply substitution to result
    | none => .var x
  | .con c => .con c
  | .app t1 t2 => .app (t1.applySubst subst) (t2.applySubst subst)
  | .arrow t1 t2 => .arrow (t1.applySubst subst) (t2.applySubst subst)
  | .forall_ x t => .forall_ x (t.applySubst (subst.filter (·.1 != x)))
  | .record fields => .record (fields.map (fun (n, t) => (n, t.applySubst subst)))

-- Free type variables
partial def Ty.freeVars : Ty → List Ident
  | .var x => [x]
  | .con _ => []
  | .app t1 t2 => t1.freeVars ++ t2.freeVars
  | .arrow t1 t2 => t1.freeVars ++ t2.freeVars
  | .forall_ x t => t.freeVars.filter (· != x)
  | .record fields => (fields.map (fun (_, t) => t.freeVars)).flatten

end Ziku

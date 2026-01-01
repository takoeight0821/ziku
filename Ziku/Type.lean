import Ziku.Syntax

namespace Ziku

/-!
# Type System

This module provides type inference utilities, using the `Ty` type from Syntax.lean.
-/

-- Type substitution
abbrev Subst := List (Ident × Ty)

-- Type scheme for let-polymorphism
structure Scheme where
  vars : List Ident  -- Quantified variables
  ty : Ty
  deriving Repr, BEq

-- Apply substitution to a type
partial def Ty.applySubst (subst : Subst) : Ty → Ty
  | .var p x => match subst.lookup x with
    | some ty => ty.applySubst subst  -- Apply substitution to result
    | none => .var p x
  | .con p c => .con p c
  | .app p t1 t2 => .app p (t1.applySubst subst) (t2.applySubst subst)
  | .arrow p t1 t2 => .arrow p (t1.applySubst subst) (t2.applySubst subst)
  | .forall_ p x t => .forall_ p x (t.applySubst (subst.filter (·.1 != x)))
  | .record p fields => .record p (fields.map (fun (n, t) => (n, t.applySubst subst)))
  | .bottom p => .bottom p  -- Bottom type is not affected by substitution

-- Free type variables
partial def Ty.freeVars : Ty → List Ident
  | .var _ x => [x]
  | .con _ _ => []
  | .app _ t1 t2 => t1.freeVars ++ t2.freeVars
  | .arrow _ t1 t2 => t1.freeVars ++ t2.freeVars
  | .forall_ _ x t => t.freeVars.filter (· != x)
  | .record _ fields => (fields.map (fun (_, t) => t.freeVars)).flatten
  | .bottom _ => []  -- Bottom type has no free variables

-- Free type variables in a scheme
def Scheme.freeVars (s : Scheme) : List Ident :=
  s.ty.freeVars.filter (fun v => !s.vars.contains v)

-- Apply substitution to a scheme
def Scheme.applySubst (subst : Subst) (s : Scheme) : Scheme :=
  let subst' := subst.filter (fun (v, _) => !s.vars.contains v)
  { s with ty := s.ty.applySubst subst' }

end Ziku

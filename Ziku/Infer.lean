import Ziku.Syntax
import Ziku.Type

namespace Ziku

abbrev TyEnv := List (String × Ty)

structure InferState where
  nextVar : Nat := 0

def freshTyVar (s : InferState) : Ty × InferState :=
  (Ty.var s.nextVar, { s with nextVar := s.nextVar + 1 })

partial def applySubst (subst : Subst) (ty : Ty) : Ty :=
  match ty with
  | Ty.int => Ty.int
  | Ty.var n =>
    match subst.lookup n with
    | some t => applySubst subst t
    | none => ty

def unify (t1 t2 : Ty) : Option Subst :=
  match t1, t2 with
  | Ty.int, Ty.int => some []
  | Ty.var n, t =>
    if t == Ty.var n then some []
    else some [(n, t)]
  | t, Ty.var n =>
    if t == Ty.var n then some []
    else some [(n, t)]

def infer (env : TyEnv) (expr : Expr) (s : InferState) : Option (Ty × Subst × InferState) :=
  match expr with
  | Expr.lit _ => some (Ty.int, [], s)
  | Expr.var x =>
    match env.lookup x with
    | some ty => some (ty, [], s)
    | none => none
  | Expr.add e1 e2 | Expr.sub e1 e2 | Expr.mul e1 e2 | Expr.div e1 e2 =>
    match infer env e1 s with
    | some (t1, subst1, s1) =>
      match infer env e2 s1 with
      | some (t2, subst2, s2) =>
        match unify t1 Ty.int with
        | some subst3 =>
          match unify t2 Ty.int with
          | some subst4 =>
            some (Ty.int, subst1 ++ subst2 ++ subst3 ++ subst4, s2)
          | none => none
        | none => none
      | none => none
    | none => none

end Ziku

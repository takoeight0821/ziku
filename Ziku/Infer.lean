import Ziku.Syntax
import Ziku.Type

namespace Ziku

/-!
# Type Inference

This module provides type inference for Ziku expressions.
Currently a simplified version that handles basic cases.
-/

-- Type environment mapping variables to types
abbrev TyEnv := List (Ident × Ty)

-- Inference state with fresh variable counter
structure InferState where
  nextVar : Nat := 0

-- Generate fresh type variable
def freshTyVar (s : InferState) : Ty × InferState :=
  let name := s!"_t{s.nextVar}"
  (.var name, { s with nextVar := s.nextVar + 1 })

-- Standard types
def tyInt : Ty := .con "Int"
def tyBool : Ty := .con "Bool"
def tyUnit : Ty := .con "Unit"
def tyString : Ty := .con "String"
def tyChar : Ty := .con "Char"
def tyFloat : Ty := .con "Float"

-- Get expected and result types for binary operators
def binOpTypes : BinOp → Ty × Ty
  | .add | .sub | .mul | .div => (tyInt, tyInt)
  | .eq | .ne | .lt | .le | .gt | .ge => (tyInt, tyBool)
  | .and | .or => (tyBool, tyBool)
  | .concat => (tyString, tyString)
  | .pipe => (tyInt, tyInt)  -- Placeholder, needs proper handling

-- Get expected and result types for unary operators
def unaryOpTypes : UnaryOp → Ty × Ty
  | .neg => (tyInt, tyInt)
  | .not => (tyBool, tyBool)

-- Basic unification (simplified)
partial def unify (t1 t2 : Ty) : Option Subst :=
  match t1, t2 with
  | .con c1, .con c2 =>
    if c1 == c2 then some [] else none
  | .var x, t =>
    some [(x, t)]
  | t, .var x =>
    some [(x, t)]
  | .arrow a1 b1, .arrow a2 b2 =>
    match unify a1 a2 with
    | some s1 =>
      match unify (b1.applySubst s1) (b2.applySubst s1) with
      | some s2 => some (s1 ++ s2)
      | none => none
    | none => none
  | .app t1 t2, .app t1' t2' =>
    match unify t1 t1' with
    | some s1 =>
      match unify (t2.applySubst s1) (t2'.applySubst s1) with
      | some s2 => some (s1 ++ s2)
      | none => none
    | none => none
  | _, _ => none

-- Type inference (simplified version)
partial def infer (env : TyEnv) (expr : Expr) (s : InferState) : Option (Ty × Subst × InferState) :=
  match expr with
  | .lit (.int _) => some (tyInt, [], s)
  | .lit (.bool _) => some (tyBool, [], s)
  | .lit .unit => some (tyUnit, [], s)
  | .lit (.string _) => some (tyString, [], s)
  | .lit (.char _) => some (tyChar, [], s)
  | .lit (.float _) => some (tyFloat, [], s)
  | .var x =>
    match env.lookup x with
    | some ty => some (ty, [], s)
    | none => none
  | .hash => none  -- Cannot infer type of # without context
  | .binOp op e1 e2 =>
    let (expectedTy, resultTy) := binOpTypes op
    match infer env e1 s with
    | some (t1, subst1, s1) =>
      match unify t1 expectedTy with
      | some subst1' =>
        match infer env e2 s1 with
        | some (t2, subst2, s2) =>
          match unify t2 expectedTy with
          | some subst2' =>
            some (resultTy, subst1 ++ subst1' ++ subst2 ++ subst2', s2)
          | none => none
        | none => none
      | none => none
    | none => none
  | .unaryOp op e =>
    let (expectedTy, resultTy) := unaryOpTypes op
    match infer env e s with
    | some (t, subst, s') =>
      match unify t expectedTy with
      | some subst' => some (resultTy, subst ++ subst', s')
      | none => none
    | none => none
  | .lam params body =>
    -- Generate fresh type variables for parameters
    let (paramTys, s') := params.foldl (fun (tys, st) _ =>
      let (ty, st') := freshTyVar st
      (tys ++ [ty], st')
    ) ([], s)
    let env' := (params.zip paramTys) ++ env
    match infer env' body s' with
    | some (bodyTy, subst, s'') =>
      let funTy := paramTys.foldr (fun t acc => .arrow t acc) bodyTy
      some (funTy.applySubst subst, subst, s'')
    | none => none
  | .app fn arg =>
    match infer env fn s with
    | some (fnTy, subst1, s1) =>
      match infer env arg s1 with
      | some (argTy, subst2, s2) =>
        let (resultTy, s3) := freshTyVar s2
        match unify (fnTy.applySubst subst2) (.arrow argTy resultTy) with
        | some subst3 =>
          some (resultTy.applySubst subst3, subst1 ++ subst2 ++ subst3, s3)
        | none => none
      | none => none
    | none => none
  | .let_ x tyOpt e1 e2 =>
    match infer env e1 s with
    | some (t1, subst1, s1) =>
      let t1' := match tyOpt with
        | some ty => ty  -- Use declared type
        | none => t1
      let env' := (x, t1') :: env
      match infer env' e2 s1 with
      | some (t2, subst2, s2) =>
        some (t2, subst1 ++ subst2, s2)
      | none => none
    | none => none
  | .letRec x tyOpt e1 e2 =>
    let (initTy, s0) := match tyOpt with
      | some ty => (ty, s)
      | none => freshTyVar s
    let env' := (x, initTy) :: env
    match infer env' e1 s0 with
    | some (t1, subst1, s1) =>
      match unify initTy t1 with
      | some substRec =>
        match infer ((x, t1.applySubst substRec) :: env) e2 s1 with
        | some (t2, subst2, s2) =>
          some (t2, subst1 ++ substRec ++ subst2, s2)
        | none => none
      | none => none
    | none => none
  | .if_ cond thenE elseE =>
    match infer env cond s with
    | some (tCond, subst1, s1) =>
      match unify tCond tyBool with
      | some subst1' =>
        match infer env thenE s1 with
        | some (tThen, subst2, s2) =>
          match infer env elseE s2 with
          | some (tElse, subst3, s3) =>
            match unify tThen tElse with
            | some subst4 =>
              some (tThen.applySubst subst4, subst1 ++ subst1' ++ subst2 ++ subst3 ++ subst4, s3)
            | none => none
          | none => none
        | none => none
      | none => none
    | none => none
  | .ann e ty =>
    match infer env e s with
    | some (inferredTy, subst, s') =>
      match unify inferredTy ty with
      | some subst' => some (ty, subst ++ subst', s')
      | none => none
    | none => none
  | .match_ _ _ => none  -- Pattern matching type inference not yet implemented
  | .codata _ => none    -- Codata type inference not yet implemented
  | .field _ _ => none   -- Field access type inference not yet implemented
  | .record _ => none    -- Record type inference not yet implemented
  | .cut _ _ => none     -- Cut type inference not yet implemented
  | .mu _ _ => none      -- Mu type inference not yet implemented

end Ziku

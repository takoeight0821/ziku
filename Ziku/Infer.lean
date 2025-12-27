import Ziku.Syntax
import Ziku.Type
import Ziku.Elaborate

namespace Ziku

/-!
# Type Inference

This module provides type inference for Ziku expressions with detailed error reporting.
Uses Hindley-Milner with let-polymorphism via Scheme types.
-/

-- Type environment mapping variables to type schemes
abbrev TyEnv := List (Ident × Scheme)

-- Inference state with fresh variable counter
structure InferState where
  nextVar : Nat := 0
  deriving Inhabited

-- Type error with source location and detailed message
inductive TypeError where
  | unificationError (pos : SourcePos) (expected : Ty) (actual : Ty) (msg : String)
  | unboundVariable (pos : SourcePos) (name : Ident)
  | occursCheck (pos : SourcePos) (varName : Ident) (ty : Ty)
  | notImplemented (pos : SourcePos) (feature : String)
  | customError (pos : SourcePos) (msg : String)
  deriving Repr

def TypeError.toString : TypeError → String
  | .unificationError pos expected actual msg =>
    s!"Type error at {pos.line}:{pos.col}: {msg}\n  Expected: {expected}\n  Actual: {actual}"
  | .unboundVariable pos name =>
    s!"Unbound variable '{name}' at {pos.line}:{pos.col}"
  | .occursCheck pos varName ty =>
    s!"Occurs check failed at {pos.line}:{pos.col}: type variable '{varName}' occurs in {ty}"
  | .notImplemented pos feature =>
    s!"Type inference not yet implemented for {feature} at {pos.line}:{pos.col}"
  | .customError pos msg =>
    s!"Error at {pos.line}:{pos.col}: {msg}"

instance : ToString TypeError := ⟨TypeError.toString⟩

-- Inference monad: State + Error
abbrev InferM := StateT InferState (Except TypeError)

-- Provide Inhabited instance for InferM (Ty × Subst)
instance : Inhabited (InferM (Ty × Subst)) where
  default := throw (.customError { line := 0, col := 0 } "Uninhabited type inference result")

-- Generate fresh type variable
def freshTyVar : InferM Ty := do
  let s ← get
  let name := s!"_t{s.nextVar}"
  set { s with nextVar := s.nextVar + 1 }
  return .var { line := 0, col := 0 } name

-- Standard types (using dummy position)
def dummyPos : SourcePos := { line := 0, col := 0 }
def tyInt : Ty := .con dummyPos "Int"
def tyBool : Ty := .con dummyPos "Bool"
def tyUnit : Ty := .con dummyPos "Unit"
def tyString : Ty := .con dummyPos "String"
def tyChar : Ty := .con dummyPos "Char"
def tyFloat : Ty := .con dummyPos "Float"

-- Get expected and result types for binary operators
-- Note: Comparison operators (.eq, .ne, .lt, .le, .gt, .ge) are currently
-- monomorphic on Int. True polymorphic equality would require type class
-- constraints (Eq, Ord), which are not yet implemented in the type system.
-- The .pipe operator is handled separately as a special case (see infer function).
def binOpTypes : BinOp → Ty × Ty
  | .add | .sub | .mul | .div => (tyInt, tyInt)
  | .eq | .ne | .lt | .le | .gt | .ge => (tyInt, tyBool)
  | .and | .or => (tyBool, tyBool)
  | .concat => (tyString, tyString)
  | .pipe => (tyInt, tyInt)  -- Not used; .pipe has special handling in infer

-- Get expected and result types for unary operators
def unaryOpTypes : UnaryOp → Ty × Ty
  | .neg => (tyInt, tyInt)
  | .not => (tyBool, tyBool)

-- Occurs check: does a type variable occur in a type?
partial def occursIn (varName : Ident) (ty : Ty) : Bool :=
  match ty with
  | .var _ x => x == varName
  | .con _ _ => false
  | .app _ t1 t2 => occursIn varName t1 || occursIn varName t2
  | .arrow _ t1 t2 => occursIn varName t1 || occursIn varName t2
  | .forall_ _ x t => if x == varName then false else occursIn varName t
  | .record _ fields => fields.any (fun (_, t) => occursIn varName t)

-- Unification with error reporting
partial def unifyAt (pos : SourcePos) (t1 t2 : Ty) : InferM Subst :=
  match t1, t2 with
  | .con _ c1, .con _ c2 =>
    if c1 == c2 then
      return []
    else
      throw $ .unificationError pos t1 t2 s!"Cannot unify type constructors '{c1}' and '{c2}'"
  | .var _ x, t =>
    if occursIn x t then
      throw $ .occursCheck pos x t
    else
      return [(x, t)]
  | t, .var _ x =>
    if occursIn x t then
      throw $ .occursCheck pos x t
    else
      return [(x, t)]
  | .arrow _ a1 b1, .arrow _ a2 b2 => do
    let s1 ← unifyAt pos a1 a2
    let s2 ← unifyAt pos (b1.applySubst s1) (b2.applySubst s1)
    return s1 ++ s2
  | .app _ t1 t2, .app _ t1' t2' => do
    let s1 ← unifyAt pos t1 t1'
    let s2 ← unifyAt pos (t2.applySubst s1) (t2'.applySubst s1)
    return s1 ++ s2
  | _, _ =>
    throw $ .unificationError pos t1 t2 s!"Cannot unify types"

-- Apply substitution to environment
def TyEnv.applySubst (subst : Subst) (env : TyEnv) : TyEnv :=
  env.map (fun (x, scheme) => (x, scheme.applySubst subst))

-- Free variables in environment
def TyEnv.freeVars (env : TyEnv) : List Ident :=
  (env.map (fun (_, scheme) => scheme.freeVars)).flatten

-- Generalize: convert a type to a scheme by quantifying over free variables
def generalize (env : TyEnv) (ty : Ty) : Scheme :=
  let envVars := env.freeVars
  let vars := ty.freeVars.filter (fun v => !envVars.contains v)
  { vars := vars, ty := ty }

-- Instantiate: convert a scheme to a type by replacing quantified variables with fresh ones
def instantiate (scheme : Scheme) : InferM Ty := do
  let mut subst : Subst := []
  for v in scheme.vars do
    let fresh ← freshTyVar
    subst := (v, fresh) :: subst
  return scheme.ty.applySubst subst

-- Pattern type checking: returns variable bindings and substitution
-- Given a pattern and expected type, extract variable bindings and unification constraints
partial def checkPattern (pat : Pat) (expectedTy : Ty) : InferM (List (Ident × Scheme) × Subst) :=
  match pat with
  | .var _ x =>
    -- Variable pattern: bind x to expected type (monomorphic)
    return ([(x, { vars := [], ty := expectedTy })], [])
  | .lit pos lit =>
    -- Literal pattern: unify with literal type
    let litTy := match lit with
      | .int _ => tyInt
      | .bool _ => tyBool
      | .string _ => tyString
      | .char _ => tyChar
      | .float _ => tyFloat
      | .unit => tyUnit
    do
      let subst ← unifyAt pos litTy expectedTy
      return ([], subst)
  | .wild _ =>
    -- Wildcard: no bindings, matches anything
    return ([], [])
  | .con pos conName _args =>
    -- Constructor pattern: need to look up constructor type
    -- For now, throw not implemented
    throw $ .notImplemented pos s!"constructor pattern '{conName}'"
  | .paren _ p =>
    -- Parenthesized: recurse
    checkPattern p expectedTy
  | .ann pos p ty => do
    -- Annotated: unify annotation with expected type, then check inner pattern
    let subst ← unifyAt pos ty expectedTy
    let (bindings, subst') ← checkPattern p (ty.applySubst subst)
    return (bindings, subst ++ subst')

-- Type inference with detailed errors
partial def infer (env : TyEnv) (expr : Expr) : InferM (Ty × Subst) :=
  match expr with
  | .lit _ (.int _) => return (tyInt, [])
  | .lit _ (.bool _) => return (tyBool, [])
  | .lit _ .unit => return (tyUnit, [])
  | .lit _ (.string _) => return (tyString, [])
  | .lit _ (.char _) => return (tyChar, [])
  | .lit _ (.float _) => return (tyFloat, [])
  | .var pos x =>
    match env.lookup x with
    | some scheme => do
      let ty ← instantiate scheme
      return (ty, [])
    | none => throw $ .unboundVariable pos x
  -- Special case for pipe operator: e1 |> e2  ≡  e2(e1)
  -- Type rule: Γ ⊢ e1 : α, Γ ⊢ e2 : α → β  ⇒  e1 |> e2 : β
  | .binOp pos .pipe e1 e2 => do
    let (t1, subst1) ← infer env e1
    let (t2, subst2) ← infer (env.applySubst subst1) e2
    let resultTy ← freshTyVar
    let subst3 ← unifyAt pos (t2.applySubst subst2) (.arrow pos (t1.applySubst subst2) resultTy)
    return (resultTy.applySubst subst3, subst1 ++ subst2 ++ subst3)
  | .binOp _pos op e1 e2 => do
    let (expectedTy, resultTy) := binOpTypes op
    let (t1, subst1) ← infer env e1
    let subst1' ← unifyAt (e1.pos) t1 expectedTy
    let (t2, subst2) ← infer (env.applySubst (subst1 ++ subst1')) e2
    let subst2' ← unifyAt (e2.pos) t2 expectedTy
    return (resultTy, subst1 ++ subst1' ++ subst2 ++ subst2')
  | .unaryOp _pos op e => do
    let (expectedTy, resultTy) := unaryOpTypes op
    let (t, subst) ← infer env e
    let subst' ← unifyAt (e.pos) t expectedTy
    return (resultTy, subst ++ subst')
  | .lam pos param body => do
    -- Generate fresh type variable for the single parameter
    let paramTy ← freshTyVar
    let paramScheme : Scheme := { vars := [], ty := paramTy }
    let env' := (param, paramScheme) :: env
    let (bodyTy, subst) ← infer env' body
    let funTy : Ty := Ty.arrow pos paramTy bodyTy
    return (funTy.applySubst subst, subst)
  | .app pos fn arg => do
    let (fnTy, subst1) ← infer env fn
    let (argTy, subst2) ← infer (env.applySubst subst1) arg
    let resultTy ← freshTyVar
    let subst3 ← unifyAt pos (fnTy.applySubst subst2) (.arrow dummyPos argTy resultTy)
    return (resultTy.applySubst subst3, subst1 ++ subst2 ++ subst3)
  | .let_ _ x tyOpt e1 e2 => do
    let (t1, subst1) ← infer env e1
    let t1' := match tyOpt with
      | some ty => ty  -- Use declared type
      | none => t1
    -- Generalize the type for let-polymorphism
    let scheme := generalize (env.applySubst subst1) t1'
    let env' := (x, scheme) :: env.applySubst subst1
    let (t2, subst2) ← infer env' e2
    return (t2, subst1 ++ subst2)
  | .letRec _ x tyOpt e1 e2 => do
    let initTy ← match tyOpt with
      | some ty => pure ty
      | none => freshTyVar
    -- For recursive bindings, use a monomorphic scheme
    let env' := (x, { vars := [], ty := initTy }) :: env
    let (t1, subst1) ← infer env' e1
    let substRec ← unifyAt (e1.pos) initTy t1
    let env'' := (x, { vars := [], ty := t1.applySubst substRec }) :: env.applySubst (subst1 ++ substRec)
    let (t2, subst2) ← infer env'' e2
    return (t2, subst1 ++ substRec ++ subst2)
  | .if_ pos cond thenE elseE => do
    let (tCond, subst1) ← infer env cond
    let subst1' ← unifyAt (cond.pos) tCond tyBool
    let env' := env.applySubst (subst1 ++ subst1')
    let (tThen, subst2) ← infer env' thenE
    let (tElse, subst3) ← infer (env'.applySubst subst2) elseE
    let subst4 ← unifyAt pos tThen tElse
    return (tThen.applySubst subst4, subst1 ++ subst1' ++ subst2 ++ subst3 ++ subst4)
  | .ann pos e ty => do
    let (inferredTy, subst) ← infer env e
    let subst' ← unifyAt pos inferredTy ty
    return (ty, subst ++ subst')
  | .match_ pos scrutinee cases => do
    -- Infer type of scrutinee
    let (scrutineeTy, subst0) ← infer env scrutinee
    let env0 := env.applySubst subst0

    -- Check each case
    let mut resultTy : Option Ty := none
    let mut accSubst := subst0

    for (pat, body) in cases do
      -- Check pattern against scrutinee type
      let (bindings, substPat) ← checkPattern pat (scrutineeTy.applySubst accSubst)
      let envCase := bindings ++ env0.applySubst (accSubst ++ substPat)

      -- Infer type of case body
      let (bodyTy, substBody) ← infer envCase body
      accSubst := accSubst ++ substPat ++ substBody

      -- Unify with previous case results
      match resultTy with
      | none => resultTy := some bodyTy
      | some prevTy =>
        let substUnify ← unifyAt pos (prevTy.applySubst substBody) bodyTy
        accSubst := accSubst ++ substUnify
        resultTy := some (bodyTy.applySubst substUnify)

    match resultTy with
    | some ty => return (ty, accSubst)
    | none => throw $ .customError pos "match expression has no cases"
  | .codata pos clauses => do
    -- Elaborate codata to record/lambda before type inference
    match elaborate pos clauses with
    | .ok elaborated => infer env elaborated
    | .error err => throw $ .customError pos (toString err)
  | .field pos e field => do
    -- Infer type of the record expression
    let (recTy, subst) ← infer env e

    -- The record must have type { field : ty, ... }
    -- For simplicity, we just check if it's a record type with the field
    match recTy.applySubst subst with
    | .record _ fields =>
      match fields.lookup field with
      | some ty => return (ty, subst)
      | none => throw $ .customError pos s!"field '{field}' not found in record"
    | _ => throw $ .customError pos s!"field access on non-record type"
  | .record pos fields => do
    -- Infer type for each field value
    let mut fieldTypes : List (Ident × Ty) := []
    let mut accSubst : Subst := []

    for (name, value) in fields do
      let (ty, subst) ← infer (env.applySubst accSubst) value
      fieldTypes := fieldTypes ++ [(name, ty)]
      accSubst := accSubst ++ subst

    return (.record pos fieldTypes, accSubst)
  | .cut pos _ _ =>
    throw $ .notImplemented pos "sequent cut"
  | .mu pos _ _ =>
    throw $ .notImplemented pos "mu abstraction"

-- Run inference with initial state
def runInfer (expr : Expr) (env : TyEnv := []) : Except TypeError (Ty × Subst) :=
  let m := infer env expr
  match m.run { nextVar := 0 } with
  | .ok ((ty, subst), _) => .ok (ty, subst)
  | .error e => .error e

end Ziku

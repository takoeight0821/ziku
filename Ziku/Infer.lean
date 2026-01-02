import Ziku.Syntax
import Ziku.Type
import Ziku.Elaborate

namespace Ziku

/-!
# Type Inference

This module provides constraint-based type inference for Ziku expressions.
Uses Hindley-Milner with let-polymorphism via Scheme types.

## Architecture

The inference is split into two phases:
1. **Constraint Generation**: Traverse AST, generate constraints without solving
2. **Constraint Solving**: Solve constraints using unification, handle bottom type propagation

This separation allows bottom type (⊥) propagation to be handled in the constraint solver,
keeping the constraint generation code simple.
-/

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

-- Type environment mapping variables to type schemes
abbrev TyEnv := List (Ident × Scheme)

-- Label environment mapping label names to their expected value types
abbrev LabelEnv := List (Ident × Ty)

/-- Type constraints generated during inference -/
inductive Constraint where
  /-- Unification constraint: t1 = t2 -/
  | unify (pos : SourcePos) (t1 : Ty) (t2 : Ty)
  /-- bottomProp制約: sourcesのいずれかが⊥型なら、targetも⊥型になる。

      これが必要な理由:
      - `goto`は戻らない式であり、その結果型は⊥（bottom type）
      - `goto(...) + 1`のような式では、gotoが⊥を返すため、
        演算全体も到達不能なコードとなり、結果も⊥であるべき
      - 単純な単一化では⊥の「伝播」を表現できない
        （⊥ = Int は成功するが、結果がIntになってしまう）
      - この制約により、⊥の伝播ロジックを制約ソルバーに集約し、
        各式の型推論コードをシンプルに保つ

      例: `label result { if true then goto(true, result) + 1 else false }`
      - goto → ⊥
      - ⊥ + 1 → bottomProp([⊥, Int], result) により result = ⊥
      - if分岐: ⊥と Boolを単一化 → Bool（⊥は任意の型と単一化可能）
      - 最終型: Bool -/
  | bottomProp (sources : List Ty) (target : Ty)
  -- Note: fieldAccess constraint removed - now handled via row polymorphism
  -- Field access `e.f` generates: unify(recTy, { f : resultTy | rowVar })
  deriving Repr

/-- State for constraint generation phase -/
structure GenState where
  nextVar : Nat := 0
  constraints : List Constraint := []
  labelEnv : LabelEnv := []
  deriving Inhabited

/-- Monad for constraint generation -/
abbrev GenM := StateT GenState (Except TypeError)

-- Nonempty instance for GenM Ty (needed for partial def)
instance : Nonempty (GenM Ty) := ⟨pure (.con { line := 0, col := 0 } "Unit")⟩

-- Generate fresh type variable
def freshTyVar : GenM Ty := do
  let s ← get
  let name := s!"_t{s.nextVar}"
  set { s with nextVar := s.nextVar + 1 }
  return .var { line := 0, col := 0 } name

-- Add a constraint to the state
def addConstraint (c : Constraint) : GenM Unit :=
  modify fun s => { s with constraints := c :: s.constraints }

-- Add a label binding to the state
def addLabelBinding (name : Ident) (ty : Ty) : GenM Unit :=
  modify fun s => { s with labelEnv := (name, ty) :: s.labelEnv }

-- Pop the most recent label binding (for scoped labels)
def popLabelBinding : GenM Unit :=
  modify fun s => { s with labelEnv := s.labelEnv.drop 1 }

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
  | .record _ fields rowTail =>
    fields.any (fun (_, t) => occursIn varName t) ||
    match rowTail with
    | some r => occursIn varName r
    | none => false
  | .bottom _ => false

-- Unification with error reporting
-- Bottom type unifies with any type (⊥ <: τ for all τ)
-- Now takes and returns nextVar for fresh variable generation during row unification
partial def unifyAt (pos : SourcePos) (t1 t2 : Ty) (nextVar : Nat) : Except TypeError (Subst × Nat) :=
  match t1, t2 with
  -- Bottom type unifies with anything
  | .bottom _, _ => .ok ([], nextVar)
  | _, .bottom _ => .ok ([], nextVar)
  | .con _ c1, .con _ c2 =>
    if c1 == c2 then
      .ok ([], nextVar)
    else
      .error $ .unificationError pos t1 t2 s!"Cannot unify type constructors '{c1}' and '{c2}'"
  | .var _ x, .var _ y =>
    -- Two variables: if same, no substitution needed; otherwise unify
    if x == y then
      .ok ([], nextVar)
    else
      .ok ([(x, .var pos y)], nextVar)
  | .var _ x, t =>
    if occursIn x t then
      .error $ .occursCheck pos x t
    else
      .ok ([(x, t)], nextVar)
  | t, .var _ x =>
    if occursIn x t then
      .error $ .occursCheck pos x t
    else
      .ok ([(x, t)], nextVar)
  | .arrow _ a1 b1, .arrow _ a2 b2 => do
    let (s1, n1) ← unifyAt pos a1 a2 nextVar
    let (s2, n2) ← unifyAt pos (b1.applySubst s1) (b2.applySubst s1) n1
    .ok (s1 ++ s2, n2)
  | .app _ t1 t2, .app _ t1' t2' => do
    let (s1, n1) ← unifyAt pos t1 t1' nextVar
    let (s2, n2) ← unifyAt pos (t2.applySubst s1) (t2'.applySubst s1) n1
    .ok (s1 ++ s2, n2)
  | .record _ fs1 r1, .record _ fs2 r2 =>
    unifyRecords pos fs1 r1 fs2 r2 nextVar
  | _, _ =>
    .error $ .unificationError pos t1 t2 s!"Cannot unify types"

where
  /-- Row unification algorithm:
      1. Find common fields → unify their types
      2. Find fields only in left record (only1)
      3. Find fields only in right record (only2)
      4. Handle row tails based on which are present -/
  unifyRecords (pos : SourcePos)
      (fs1 : List (Ident × Ty)) (r1 : Option Ty)
      (fs2 : List (Ident × Ty)) (r2 : Option Ty)
      (nextVar : Nat) : Except TypeError (Subst × Nat) := do
    -- Separate common and unique fields
    let common := fs1.filter (fun (l, _) => fs2.any (fun (l', _) => l == l'))
    let only1 := fs1.filter (fun (l, _) => !fs2.any (fun (l', _) => l == l'))
    let only2 := fs2.filter (fun (l, _) => !fs1.any (fun (l', _) => l == l'))

    -- Unify common fields first
    let (commonSubst, n1) ← common.foldlM (init := ([], nextVar)) fun (subst, n) (l, t1) =>
      match fs2.find? (fun (l', _) => l == l') with
      | some (_, t2) =>
        match unifyAt pos (t1.applySubst subst) (t2.applySubst subst) n with
        | .ok (s, n') => .ok (subst ++ s, n')
        | .error e => .error e
      | none => .ok (subst, n)  -- Should not happen since we filtered for common

    -- Handle tails based on which are present
    match r1, r2 with
    | none, none =>
      -- Both closed: only1 and only2 must be empty
      if only1.isEmpty && only2.isEmpty then
        .ok (commonSubst, n1)
      else
        .error $ .unificationError pos
          (.record dummyPos fs1 none) (.record dummyPos fs2 none)
          s!"Record field mismatch: cannot unify closed records with different fields"
    | some row1, none =>
      -- Left has tail, right is closed: row1 must equal { only2 | ∅ }
      if only1.isEmpty then
        -- row1 = { only2 fields }
        let (tailSubst, n2) ← unifyAt pos row1 (.record dummyPos only2 none) n1
        .ok (commonSubst ++ tailSubst, n2)
      else
        .error $ .unificationError pos
          (.record dummyPos fs1 (some row1)) (.record dummyPos fs2 none)
          s!"Record field mismatch: left has extra fields {only1.map (·.1)}"
    | none, some row2 =>
      -- Right has tail, left is closed: row2 must equal { only1 | ∅ }
      if only2.isEmpty then
        -- row2 = { only1 fields }
        let (tailSubst, n2) ← unifyAt pos row2 (.record dummyPos only1 none) n1
        .ok (commonSubst ++ tailSubst, n2)
      else
        .error $ .unificationError pos
          (.record dummyPos fs1 none) (.record dummyPos fs2 (some row2))
          s!"Record field mismatch: right has extra fields {only2.map (·.1)}"
    | some row1, some row2 =>
      -- Both have tails: create fresh row variable ρ
      -- row1 = { only2 | ρ }
      -- row2 = { only1 | ρ }
      let freshRow := Ty.var dummyPos s!"_r{n1}"
      let n2 := n1 + 1
      let (s1, n3) ← unifyAt pos row1 (Ty.record dummyPos only2 (some freshRow)) n2
      let row1Rec : Ty := Ty.record dummyPos only1 (some freshRow)
      let (s2, n4) ← unifyAt pos (row2.applySubst s1) (row1Rec.applySubst s1) n3
      .ok (commonSubst ++ s1 ++ s2, n4)

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
def instantiate (scheme : Scheme) : GenM Ty := do
  let mut subst : Subst := []
  for v in scheme.vars do
    let fresh ← freshTyVar
    subst := (v, fresh) :: subst
  return scheme.ty.applySubst subst

-- Convert a Ty.forall_ to a Scheme by extracting quantified variables
-- Used for explicit forall annotations like `let id : forall a. a -> a = ...`
def tyToScheme (ty : Ty) : Scheme :=
  match ty with
  | .forall_ _ x inner =>
    let innerScheme := tyToScheme inner
    { vars := x :: innerScheme.vars, ty := innerScheme.ty }
  | .var _ _ => { vars := [], ty := ty }
  | .con _ _ => { vars := [], ty := ty }
  | .app _ _ _ => { vars := [], ty := ty }
  | .arrow _ _ _ => { vars := [], ty := ty }
  | .record _ _ _ => { vars := [], ty := ty }
  | .bottom _ => { vars := [], ty := ty }

-- Instantiate a Ty: if it's a forall type, replace quantified variables with fresh ones
-- This handles explicit forall types in annotations like `(e : forall a. a -> a)`
partial def instantiateTy (ty : Ty) : GenM Ty :=
  match ty with
  | .forall_ _ x inner => do
    let fresh ← freshTyVar
    let body := inner.applySubst [(x, fresh)]
    instantiateTy body  -- Handle nested foralls
  | _ => pure ty

-- Pattern type checking: returns variable bindings
-- Given a pattern and expected type, extract variable bindings and add unification constraints
partial def checkPattern (pat : Pat) (expectedTy : Ty) : GenM (List (Ident × Scheme)) :=
  match pat with
  | .var _ x =>
    -- Variable pattern: bind x to expected type (monomorphic)
    return [(x, { vars := [], ty := expectedTy })]
  | .lit pos lit => do
    -- Literal pattern: unify with literal type
    let litTy := match lit with
      | .int _ => tyInt
      | .bool _ => tyBool
      | .string _ => tyString
      | .char _ => tyChar
      | .float _ => tyFloat
      | .unit => tyUnit
    addConstraint (.unify pos litTy expectedTy)
    return []
  | .wild _ =>
    -- Wildcard: no bindings, matches anything
    return []
  | .con pos conName _args =>
    -- Constructor pattern: need to look up constructor type
    -- For now, throw not implemented
    throw $ .notImplemented pos s!"constructor pattern '{conName}'"
  | .paren _ p =>
    -- Parenthesized: recurse
    checkPattern p expectedTy
  | .ann pos p ty => do
    -- Annotated: unify annotation with expected type, then check inner pattern
    addConstraint (.unify pos ty expectedTy)
    checkPattern p ty

-- Constraint generation phase: traverse AST and generate constraints
-- Returns the type of the expression (constraints are added to state)
partial def genConstraints (env : TyEnv) (expr : Expr) : GenM Ty :=
  match expr with
  | .lit _ (.int _) => return tyInt
  | .lit _ (.bool _) => return tyBool
  | .lit _ .unit => return tyUnit
  | .lit _ (.string _) => return tyString
  | .lit _ (.char _) => return tyChar
  | .lit _ (.float _) => return tyFloat
  | .var pos x =>
    match env.lookup x with
    | some scheme => instantiate scheme
    | none => throw $ .unboundVariable pos x
  -- Special case for pipe operator: e1 |> e2  ≡  e2(e1)
  -- Type rule: Γ ⊢ e1 : α, Γ ⊢ e2 : α → β  ⇒  e1 |> e2 : β
  | .binOp pos .pipe e1 e2 => do
    let t1 ← genConstraints env e1
    let t2 ← genConstraints env e2
    let resultTy ← freshTyVar
    addConstraint (.unify pos t2 (.arrow pos t1 resultTy))
    addConstraint (.bottomProp [t1, t2] resultTy)
    return resultTy
  | .binOp pos op e1 e2 => do
    let (expectedTy, normalResultTy) := binOpTypes op
    let t1 ← genConstraints env e1
    addConstraint (.unify (e1.pos) t1 expectedTy)
    let t2 ← genConstraints env e2
    addConstraint (.unify (e2.pos) t2 expectedTy)
    let resultTy ← freshTyVar
    addConstraint (.unify pos resultTy normalResultTy)
    addConstraint (.bottomProp [t1, t2] resultTy)
    return resultTy
  | .unaryOp pos op e => do
    let (expectedTy, normalResultTy) := unaryOpTypes op
    let t ← genConstraints env e
    addConstraint (.unify (e.pos) t expectedTy)
    let resultTy ← freshTyVar
    addConstraint (.unify pos resultTy normalResultTy)
    addConstraint (.bottomProp [t] resultTy)
    return resultTy
  | .lam pos param body => do
    -- Generate fresh type variable for the single parameter
    let paramTy ← freshTyVar
    let paramScheme : Scheme := { vars := [], ty := paramTy }
    let env' := (param, paramScheme) :: env
    let bodyTy ← genConstraints env' body
    return .arrow pos paramTy bodyTy
  | .app pos fn arg => do
    let fnTy ← genConstraints env fn
    let argTy ← genConstraints env arg
    let resultTy ← freshTyVar
    addConstraint (.unify pos fnTy (.arrow pos argTy resultTy))
    addConstraint (.bottomProp [fnTy, argTy] resultTy)
    return resultTy
  | .let_ pos x tyOpt e1 e2 => do
    let t1 ← genConstraints env e1
    -- Determine the scheme for the binding:
    -- If an explicit forall annotation is given, use it for polymorphism
    let scheme := match tyOpt with
      | some ty =>
        let s := tyToScheme ty
        if s.vars.isEmpty then { vars := [], ty := t1 }
        else s  -- Use explicit forall as polymorphic scheme
      | none => { vars := [], ty := t1 }
    -- Unify the inferred type with the instantiated annotation
    match tyOpt with
    | some ty => do
      let instantiated ← instantiateTy ty
      addConstraint (.unify pos t1 instantiated)
    | none => pure ()
    let env' := (x, scheme) :: env
    genConstraints env' e2
  | .letRec pos x tyOpt e1 e2 => do
    let initTy ← match tyOpt with
      | some ty => pure ty
      | none => freshTyVar
    -- For recursive bindings, use a monomorphic scheme
    let env' := (x, { vars := [], ty := initTy }) :: env
    let t1 ← genConstraints env' e1
    addConstraint (.unify pos initTy t1)
    genConstraints env' e2
  | .if_ pos cond thenE elseE => do
    let tCond ← genConstraints env cond
    addConstraint (.unify (cond.pos) tCond tyBool)
    let tThen ← genConstraints env thenE
    let tElse ← genConstraints env elseE
    let resultTy ← freshTyVar
    -- Both branches unify with result (bottom is handled in solver)
    addConstraint (.unify pos tThen resultTy)
    addConstraint (.unify pos tElse resultTy)
    return resultTy
  | .ann pos e ty => do
    let inferredTy ← genConstraints env e
    let instantiatedTy ← instantiateTy ty
    addConstraint (.unify pos inferredTy instantiatedTy)
    return instantiatedTy
  | .match_ pos scrutinee cases => do
    -- Infer type of scrutinee
    let scrutineeTy ← genConstraints env scrutinee
    let resultTy ← freshTyVar

    -- Check each case
    for (pat, body) in cases do
      -- Check pattern against scrutinee type
      let bindings ← checkPattern pat scrutineeTy
      let envCase := bindings ++ env

      -- Infer type of case body
      let bodyTy ← genConstraints envCase body
      addConstraint (.unify pos bodyTy resultTy)

    return resultTy
  | .codata pos clauses => do
    -- Elaborate codata to record/lambda before type inference
    match elaborate pos clauses with
    | .ok elaborated => genConstraints env elaborated
    | .error err => throw $ .customError pos (toString err)
  | .field pos e field => do
    -- Infer type of the record expression
    let recTy ← genConstraints env e
    -- Create fresh type variable for the result
    let resultTy ← freshTyVar
    -- Create fresh row variable for remaining fields (row polymorphism)
    let rowVar ← freshTyVar
    -- Unify record type with { field : resultTy | rowVar }
    addConstraint (.unify pos recTy (.record pos [(field, resultTy)] (some rowVar)))
    -- Propagate bottom if record is bottom
    addConstraint (.bottomProp [recTy] resultTy)
    return resultTy
  | .record pos fields => do
    -- Infer type for each field value
    let mut fieldTypes : List (Ident × Ty) := []
    for (name, value) in fields do
      let ty ← genConstraints env value
      fieldTypes := fieldTypes ++ [(name, ty)]
    return .record pos fieldTypes none  -- Closed record (no row tail)
  | .cut pos _ _ =>
    throw $ .notImplemented pos "sequent cut"
  | .mu pos _ _ =>
    throw $ .notImplemented pos "mu abstraction"
  | .hash pos =>
    throw $ .notImplemented pos "hash self-reference (should be substituted during elaboration)"
  | .label pos name body => do
    -- label name { body }: Create a label that can be jumped to with goto
    -- The label's expected value type is unified with the body's type
    let labelTy ← freshTyVar
    addLabelBinding name labelTy
    let bodyTy ← genConstraints env body
    addConstraint (.unify pos bodyTy labelTy)
    popLabelBinding
    return labelTy
  | .goto pos value labelName => do
    -- goto(value, name): Jumps to the label, never returns.
    -- Returns bottom type since the expression never produces a value.
    let valueTy ← genConstraints env value
    let s ← get
    match s.labelEnv.lookup labelName with
    | some labelTy =>
        -- Value type must match label's expected type
        addConstraint (.unify pos valueTy labelTy)
        -- goto returns bottom type (never returns)
        return .bottom pos
    | none => throw $ .unboundVariable pos labelName

/-! ## Constraint Solving

The constraint solver processes constraints generated by `genConstraints`.
It handles:
1. `unify` constraints using standard unification
2. `bottomProp` constraints by propagating bottom type through dependencies

The key insight for bottom type propagation:
- When `⊥ = τ` is unified, it succeeds (⊥ unifies with anything)
- But we track which type variables are "tainted" by bottom
- At the end, tainted variables become bottom type in the final substitution
-/

/-- State for constraint solving -/
structure SolverState where
  subst : Subst := []
  /-- Type variables that are known to be bottom (either directly or through propagation) -/
  bottomVars : List Ident := []
  /-- Counter for generating fresh type variables during row unification -/
  nextVar : Nat := 0
  deriving Inhabited

/-- Check if a type is or contains a bottom type variable -/
partial def isBottomTainted (bottomVars : List Ident) : Ty → Bool
  | .bottom _ => true
  | .var _ x => bottomVars.contains x
  | .con _ _ => false
  | .app _ t1 t2 => isBottomTainted bottomVars t1 || isBottomTainted bottomVars t2
  | .arrow _ t1 t2 => isBottomTainted bottomVars t1 || isBottomTainted bottomVars t2
  | .forall_ _ x t => if bottomVars.contains x then false else isBottomTainted bottomVars t
  | .record _ fields rowTail =>
    fields.any (fun (_, t) => isBottomTainted bottomVars t) ||
    match rowTail with
    | some r => isBottomTainted bottomVars r
    | none => false

/-- Extract type variable name if the type is a variable -/
def Ty.varName? : Ty → Option Ident
  | .var _ x => some x
  | _ => none

/-- Compose two substitutions: apply s1 first, then s2 -/
def composeSubst (s1 s2 : Subst) : Subst :=
  s1.map (fun (x, t) => (x, t.applySubst s2)) ++ s2.filter (fun (x, _) => !s1.any (·.1 == x))

/-- Solve a single unify constraint, tracking bottom propagation -/
partial def solveUnify (pos : SourcePos) (t1 t2 : Ty) (state : SolverState)
    : Except TypeError SolverState := do
  let t1' := t1.applySubst state.subst
  let t2' := t2.applySubst state.subst

  -- Check if either type is the actual bottom type (not just bottom-tainted)
  -- When unifying with bottom, we succeed without adding substitution
  -- This allows the other branch in if-expressions to determine the type
  if t1'.isBottom || t2'.isBottom then
    -- Just succeed - don't mark the other side as bottom
    -- Bottom propagation through expressions is handled by bottomProp constraints
    return state

  -- Check if either type is bottom-tainted (variable in bottomVars)
  let t1Tainted := isBottomTainted state.bottomVars t1'
  let t2Tainted := isBottomTainted state.bottomVars t2'

  -- If one side is bottom-tainted (but not the actual bottom type),
  -- unification succeeds and we propagate the taint
  if t1Tainted || t2Tainted then
    let newBottomVars :=
      if t1Tainted then
        match t2'.varName? with
        | some x => if state.bottomVars.contains x then [] else [x]
        | none => []
      else
        match t1'.varName? with
        | some x => if state.bottomVars.contains x then [] else [x]
        | none => []
    return { state with bottomVars := state.bottomVars ++ newBottomVars }

  -- Normal case: neither side is bottom-related, perform standard unification
  match unifyAt pos t1' t2' state.nextVar with
  | .ok (newSubst, newNextVar) =>
    .ok { subst := composeSubst state.subst newSubst, bottomVars := state.bottomVars, nextVar := newNextVar }
  | .error e => .error e

/-- Solve a bottomProp constraint: if any source is bottom, mark target as bottom -/
def solveBottomProp (sources : List Ty) (target : Ty) (state : SolverState) : SolverState :=
  let sources' := sources.map (·.applySubst state.subst)
  let anySourceBottom := sources'.any (isBottomTainted state.bottomVars)

  if anySourceBottom then
    let target' := target.applySubst state.subst
    match target'.varName? with
    | some x =>
      if state.bottomVars.contains x then state
      else { state with bottomVars := x :: state.bottomVars }
    | none => state  -- Target already resolved to concrete type
  else state

/-- Collect all bottomProp constraints for reference during solving -/
def collectBottomProps (constraints : List Constraint) : List (List Ty × Ty) :=
  constraints.filterMap fun
    | .bottomProp sources target => some (sources, target)
    | _ => none

/-- Apply all bottomProp constraints once -/
def applyBottomProps (bottomProps : List (List Ty × Ty)) (state : SolverState) : SolverState :=
  bottomProps.foldl (fun s (sources, target) => solveBottomProp sources target s) state

/-- Propagate bottom through all bottomProp constraints until fixpoint -/
partial def propagateBottomFixpoint (bottomProps : List (List Ty × Ty)) (state : SolverState) : SolverState :=
  let newState := applyBottomProps bottomProps state
  if newState.bottomVars.length > state.bottomVars.length then
    propagateBottomFixpoint bottomProps newState
  else
    newState

/-- Solve all constraints with interleaved bottom propagation -/
def solveConstraints (constraints : List Constraint) (initNextVar : Nat := 0) : Except TypeError SolverState := do
  let bottomProps := collectBottomProps constraints
  let mut state : SolverState := { nextVar := initNextVar }

  -- Process unify constraints in order, propagating bottom after each
  for c in constraints do
    match c with
    | .unify pos t1 t2 =>
      -- Perform unification (solveUnify handles bottom logic)
      state ← solveUnify pos t1 t2 state

      -- Propagate bottom through bottomProp constraints
      state := propagateBottomFixpoint bottomProps state

    | .bottomProp _ _ =>
      -- Handled by propagateBottomFixpoint
      pure ()

  -- Final bottom propagation pass
  state := propagateBottomFixpoint bottomProps state

  return state

/-- Finalize a type by replacing bottom-tainted variables with bottom -/
partial def finalizeTy (bottomVars : List Ident) : Ty → Ty
  | .var p x => if bottomVars.contains x then .bottom p else .var p x
  | .con p c => .con p c
  | .app p t1 t2 => .app p (finalizeTy bottomVars t1) (finalizeTy bottomVars t2)
  | .arrow p t1 t2 => .arrow p (finalizeTy bottomVars t1) (finalizeTy bottomVars t2)
  | .forall_ p x t => .forall_ p x (finalizeTy (bottomVars.filter (· != x)) t)
  | .record p fields rowTail =>
    .record p
      (fields.map fun (n, t) => (n, finalizeTy bottomVars t))
      (rowTail.map (finalizeTy bottomVars))
  | .bottom p => .bottom p

/-- Run inference: generates constraints, solves them, returns final type -/
def runInfer (expr : Expr) (env : TyEnv := []) : Except TypeError (Ty × Subst) := do
  -- Phase 1: Generate constraints
  let initState : GenState := { nextVar := 0, constraints := [], labelEnv := [] }
  match (genConstraints env expr).run initState with
  | .error e => .error e
  | .ok (ty, finalGenState) =>
    -- Phase 2: Solve constraints
    let constraints := finalGenState.constraints.reverse  -- Process in order generated
    -- Pass nextVar to solver for fresh variable generation during row unification
    match solveConstraints constraints finalGenState.nextVar with
    | .error e => .error e
    | .ok solverState =>
      -- Phase 3: Apply substitution and finalize (handle bottom)
      let resultTy := ty.applySubst solverState.subst
      let finalTy := finalizeTy solverState.bottomVars resultTy
      -- Apply substitution again to ensure full resolution of nested types
      let fullyResolved := finalTy.applySubst solverState.subst
      .ok (fullyResolved, solverState.subst)

end Ziku

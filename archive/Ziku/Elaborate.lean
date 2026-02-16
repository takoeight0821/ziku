import Ziku.Syntax
import Ziku.FreshName

namespace Ziku

/-!
# Codata Elaboration

This module implements the codata elaboration pass that transforms codata expressions
into records and curried lambdas before type inference and evaluation.

Based on anma's copattern flattening algorithm:
- Field copatterns → Records
- Call copatterns → Lambdas
- Multi-param calls are desugared to nested lambdas
- Pattern guards generate outer match expressions

## Algorithm Overview

1. Classify copatterns by first accessor (field vs. call)
2. For field accessors: generate record with recursive elaboration
3. For call accessors: generate lambda with recursive elaboration
4. For pattern guards: generate outer match expression
5. Reject mixed accessor kinds with descriptive error
-/

-- Elaboration error with source location
/-- Represents an error that occurred during codata elaboration. -/
inductive ElaborateError where
  /-- Error for mixed field and call accessors in the same codata block. -/
  | mixedAccessors (pos : SourcePos) (msg : String)
  /-- Error for an empty copattern where one was expected. -/
  | emptyCopattern (pos : SourcePos)
  /-- General elaboration error with a custom message. -/
  | customError (pos : SourcePos) (msg : String)
  deriving Repr, Nonempty

/-- Returns the string representation of an elaboration error. -/
def ElaborateError.toString : ElaborateError → String
  | .mixedAccessors pos msg =>
    s!"Elaboration error at {pos.line}:{pos.col}: {msg}"
  | .emptyCopattern pos =>
    s!"Empty copattern at {pos.line}:{pos.col}"
  | .customError pos msg =>
    s!"Elaboration error at {pos.line}:{pos.col}: {msg}"

instance : ToString ElaborateError := ⟨ElaborateError.toString⟩

/-- Elaboration monad with a counter for generating fresh hygienic names. -/
abbrev ElabM := StateT Nat (Except ElaborateError)

/-- Generate a fresh hygienic variable name for elaboration. -/
def elabFresh (base : String) : ElabM Ident := do
  let n ← get
  set (n + 1)
  return FreshName.fresh base n

-- Classification of copattern accessors
/-- Represents the kind of a copattern accessor (field vs. call). -/
inductive AccessorKind where
  /-- Field accessor (e.g., '.field'). -/
  | field : AccessorKind
  /-- Application accessor (e.g., '(arg)'). -/
  | call : AccessorKind
  deriving Repr, BEq, DecidableEq

-- Get the kind of an accessor
/-- Returns the kind of a given accessor. -/
def Accessor.kind : Accessor → AccessorKind
  | .field _ => .field
  | .apply _ => .call

-- Clause with pattern guards, copattern, and body
/-- Represents a single clause in a codata block. -/
structure Clause where
  /-- List of patterns (pattern guards). -/
  patterns : List Pat
  /-- Sequence of accessors (copattern). -/
  copattern : Copattern
  /-- Body of the clause. -/
  body : Expr
  deriving Repr, BEq

-- Make Clause inhabited for head!
instance : Inhabited Clause where
  default := {
    patterns := [],
    copattern := [],
    body := .lit synthesizedPos .unit
  }

-- Get the kind of the first accessor in a copattern, if any
/-- Returns the kind of the first accessor in a copattern, if any. -/
def Copattern.firstKind? : Copattern → Option AccessorKind
  | [] => none
  | acc :: _ => some acc.kind

-- Check if all copatterns have the same first accessor kind
/-- Returns the shared accessor kind if all clauses have the same kind of first accessor. -/
def allSameKind (clauses : List Clause) : Option AccessorKind :=
  match clauses with
  | [] => none
  | first :: rest =>
    let firstKind := first.copattern.firstKind?
    if rest.all (fun c => c.copattern.firstKind? == firstKind) then
      firstKind
    else
      none

-- Structural equality for patterns ignoring source positions
partial def Pat.structEq : Pat → Pat → Bool
  | .var _ x, .var _ y => x == y
  | .lit _ l1, .lit _ l2 => l1 == l2
  | .wild _, .wild _ => true
  | .con _ c1 ps1, .con _ c2 ps2 =>
    c1 == c2 && ps1.length == ps2.length && (ps1.zip ps2).all (fun (p1, p2) => Pat.structEq p1 p2)
  | .paren _ p1, .paren _ p2 => Pat.structEq p1 p2
  | .ann _ p1 _, .ann _ p2 _ => Pat.structEq p1 p2
  | _, _ => false

-- Group clauses by their copattern
/-- Groups a list of clauses by their shared copattern sequence. -/
def groupByCopattern (clauses : List Clause) : List (Copattern × List Clause) :=
  clauses.foldl (fun groups clause =>
    match groups.find? (fun (cp, _) => cp == clause.copattern) with
    | some _ =>
      groups.map (fun (cp, cs) =>
        if cp == clause.copattern then (cp, cs ++ [clause]) else (cp, cs))
    | none => groups ++ [(clause.copattern, [clause])]
  ) []

-- Build a match expression from clauses with patterns
-- Each clause should have exactly one pattern
/-- Constructs a match expression from a list of clauses that have pattern guards. -/
def buildMatchExpr (pos : SourcePos) (argName : Ident) (clauses : List Clause)
    : ElabM Expr := do
  let cases ← clauses.mapM fun clause =>
    match clause.patterns with
    | [pat] => pure (pat, clause.body)
    | [] => throw (.customError pos "expected pattern in clause")
    | _ => throw (.customError pos "multiple patterns not yet supported")
  pure (.match_ pos (.var pos argName) cases)

-- Inhabited instance for Except ElaborateError Expr
instance : Inhabited (Except ElaborateError Expr) where
  default := throw (.customError synthesizedPos "uninhabited")

-- Inhabited instance for ElabM Expr
instance : Inhabited (ElabM Expr) where
  default := throw (.customError synthesizedPos "uninhabited")

-- Rename a free variable in an expression (simple alpha-renaming)
partial def renameVar (oldName newName : Ident) : Expr → Expr
  | .var p x => if x == oldName then .var p newName else .var p x
  | .lam p x isCov body =>
    if x == oldName then .lam p x isCov body  -- shadowed
    else .lam p x isCov (renameVar oldName newName body)
  | .app p fn arg isCov => .app p (renameVar oldName newName fn) (renameVar oldName newName arg) isCov
  | .binOp p op e1 e2 => .binOp p op (renameVar oldName newName e1) (renameVar oldName newName e2)
  | .unaryOp p op e => .unaryOp p op (renameVar oldName newName e)
  | .let_ p x ty e1 e2 =>
    let e1' := renameVar oldName newName e1
    if x == oldName then .let_ p x ty e1' e2  -- shadowed in e2
    else .let_ p x ty e1' (renameVar oldName newName e2)
  | .letRec p x ty e1 e2 =>
    if x == oldName then .letRec p x ty e1 e2  -- shadowed in both
    else .letRec p x ty (renameVar oldName newName e1) (renameVar oldName newName e2)
  | .match_ p e cases =>
    .match_ p (renameVar oldName newName e) (cases.map fun (pat, body) =>
      -- If pattern binds oldName, don't rename in body
      if patBinds oldName pat then (pat, body)
      else (pat, renameVar oldName newName body))
  | .field p e f => .field p (renameVar oldName newName e) f
  | .ann p e ty => .ann p (renameVar oldName newName e) ty
  | .record p fields => .record p (fields.map fun (n, e) => (n, renameVar oldName newName e))
  | .if_ p c t f => .if_ p (renameVar oldName newName c) (renameVar oldName newName t) (renameVar oldName newName f)
  | .label p name body =>
    if name == oldName then .label p name body  -- shadowed
    else .label p name (renameVar oldName newName body)
  | .goto p e1 e2 => .goto p (renameVar oldName newName e1) (renameVar oldName newName e2)
  | .con p name args => .con p name (args.map (renameVar oldName newName))
  | .codata p clauses => .codata p (clauses.map fun (pats, copat, body) =>
      -- If any pattern binds oldName, don't rename in body
      if pats.any (patBinds oldName) then (pats, copat, body)
      else (pats, copat, renameVar oldName newName body))
  | e => e  -- lit, hash, extern, import_
where
  patBinds (name : Ident) : Pat → Bool
    | .var _ x => x == name
    | .con _ _ ps => ps.any (patBinds name)
    | .paren _ p => patBinds name p
    | .ann _ p _ => patBinds name p
    | _ => false

mutual

-- Elaborate pattern guards into lambda + match + codata
-- { pat1 #copat1 => body1, pat2 #copat2 => body2 } becomes:
-- \arg => { copat1 = match arg with | pat1 => body1, copat2 = match arg with | pat2 => body2 }
/-- Elaborates pattern guards into an equivalent expression using lambdas and match. -/
partial def elaborateWithPatternGuards (pos : SourcePos) (clauses : List Clause)
    : ElabM Expr := do
  -- Validate: all clauses must have exactly one pattern
  for clause in clauses do
    if clause.patterns.isEmpty then
      throw (.customError pos "mixed pattern guards: some clauses have patterns, some don't")
    if clause.patterns.length > 1 then
      throw (.customError pos "multiple pattern arguments not yet supported")

  -- Generate fresh argument name
  let argName ← elabFresh "pat_arg"

  -- Group clauses by copattern
  let groups := groupByCopattern clauses

  -- For each copattern group, create a match expression
  let mut newClauses : List Clause := []
  for (copat, groupClauses) in groups do
    let matchExpr ← buildMatchExpr pos argName groupClauses
    newClauses := newClauses ++ [{ patterns := [], copattern := copat, body := matchExpr }]

  -- Elaborate the transformed clauses (now without pattern guards)
  let innerExpr ← elaborate pos (newClauses.map fun c => (c.patterns, c.copattern, c.body))

  -- Wrap in lambda for the argument
  pure (.lam pos argName false innerExpr)

-- Elaborate pattern guards into a match expression
/-- Handles the base case of pattern matching during elaboration. -/
partial def elaboratePatternMatch (pos : SourcePos) (clauses : List Clause) : ElabM Expr :=
  if clauses.isEmpty then
    throw (.emptyCopattern pos)
  else if clauses.length == 1 && clauses.head!.patterns.isEmpty then
    -- Single clause with no patterns, just return the body
    pure clauses.head!.body
  else if clauses.all (fun c => c.patterns.isEmpty) then
    -- Multiple clauses without patterns - ambiguous
    throw (.customError pos "multiple clauses without pattern guards")
  else if clauses.any (fun c => !c.patterns.isEmpty) then
    -- Some clauses have patterns - elaborate them
    elaborateWithPatternGuards pos clauses
  else
    throw (.customError pos "pattern guards not yet implemented")

-- Elaborate a codata expression into records and lambdas
-- All helper functions are inlined to avoid partial def issues
/-- Recursively elaborates a codata expression into nested records and lambdas. -/
partial def elaborate (pos : SourcePos) (rawClauses : List (List Pat × Copattern × Expr)) : ElabM Expr :=
  -- Convert to clause structure
  let clauses : List Clause := rawClauses.map (fun (pats, copat, body) =>
    { patterns := pats, copattern := copat, body := body })

  -- If all copatterns are empty, we have pattern guards only
  if clauses.all (fun c => c.copattern.isEmpty) then
    elaboratePatternMatch pos clauses
  else
    -- Check if all first accessors are the same kind
    match allSameKind clauses with
    | none =>
      -- Mixed accessors or empty clauses
      if clauses.isEmpty then
        throw (.emptyCopattern pos)
      else
        throw (.mixedAccessors pos "incompatible copattern kinds: mixing field accessors with function calls")
    | some .field => do
      -- Elaborate field copatterns into a record
      -- Group clauses by field name
      let mut fieldGroups : List (Ident × List Clause) := []

      for clause in clauses do
        match clause.copattern with
        | .field fieldName :: restCopat =>
          -- Create new clause with remaining copattern
          let newClause : Clause := {
            patterns := clause.patterns,
            copattern := restCopat,
            body := clause.body
          }
          -- Add to group
          match fieldGroups.lookup fieldName with
          | some existing =>
            fieldGroups := fieldGroups.filter (fun (n, _) => n != fieldName)
            fieldGroups := (fieldName, existing ++ [newClause]) :: fieldGroups
          | none =>
            fieldGroups := (fieldName, [newClause]) :: fieldGroups
        | _ =>
          throw (.customError pos "expected field accessor")

      -- Elaborate each field group recursively
      let mut fields : List (Ident × Expr) := []
      for (fieldName, fieldClauses) in fieldGroups do
        let fieldExpr ← elaborate pos (fieldClauses.map (fun c => (c.patterns, c.copattern, c.body)))
        fields := (fieldName, fieldExpr) :: fields

      pure (.record pos fields.reverse)
    | some .call => do
      -- Elaborate call copatterns into curried lambdas
      -- Check if all first accessors are simple variable patterns
      let allSimpleVar := clauses.all fun c =>
        match c.copattern with
        | .apply (.var _ _) :: _ => true
        | _ => false
      if allSimpleVar then
        -- All simple variable patterns: use the first clause's name for the lambda,
        -- and rename other variables in their bodies to match
        match clauses.head? with
        | none => throw (.emptyCopattern pos)
        | some firstClause =>
          match firstClause.copattern with
          | .apply (.var _ paramName) :: _ =>
            let mut lamClauses : List Clause := []
            for clause in clauses do
              match clause.copattern with
              | .apply (.var _ varName) :: restCopat =>
                -- Rename variable in body if different from paramName
                let body := if varName == paramName then clause.body
                            else renameVar varName paramName clause.body
                lamClauses := lamClauses ++ [{
                  patterns := clause.patterns,
                  copattern := restCopat,
                  body := body
                }]
              | _ => throw (.customError pos "expected call accessor")
            let bodyExpr ← elaborate pos (lamClauses.map (fun c => (c.patterns, c.copattern, c.body)))
            pure (.lam pos paramName false bodyExpr)
          | _ => throw (.customError pos "expected call accessor")
      else
        -- Complex patterns (e.g., constructors): generate \fresh => match fresh { pat => ... }
        let freshName ← elabFresh "copat_arg"
        -- Collect (pattern, remaining clauses) pairs grouped by pattern
        let mut patGroups : List (Pat × List Clause) := []
        for clause in clauses do
          match clause.copattern with
          | .apply p :: restCopat =>
            let newClause : Clause := {
              patterns := clause.patterns,
              copattern := restCopat,
              body := clause.body
            }
            match patGroups.find? (fun (gp, _) => Pat.structEq gp p) with
            | some _ =>
              patGroups := patGroups.map (fun (gp, cs) =>
                if Pat.structEq gp p then (gp, cs ++ [newClause]) else (gp, cs))
            | none =>
              patGroups := patGroups ++ [(p, [newClause])]
          | _ => throw (.customError pos "expected call accessor")
        -- For each pattern group, recursively elaborate and create a match case
        let mut matchCases : List (Pat × Expr) := []
        for (p, groupClauses) in patGroups do
          let bodyExpr ← elaborate pos (groupClauses.map (fun c => (c.patterns, c.copattern, c.body)))
          matchCases := matchCases ++ [(p, bodyExpr)]
        let matchExpr := Expr.match_ pos (Expr.var pos freshName) matchCases
        pure (.lam pos freshName false matchExpr)

end -- mutual

-- Top-level elaboration entry point
/-- Top-level entry point for elaborating a single expression. -/
def elaborateExpr : Expr → Except ElaborateError Expr
  | .codata pos clauses => (elaborate pos clauses).run' 0
  | e => pure e

-- Recursively elaborate all codata expressions in an expression (internal, uses ElabM)
partial def elaborateAllM : Expr → ElabM Expr
  | .codata pos clauses => do
    let elaborated ← elaborate pos clauses
    elaborateAllM elaborated
  | .binOp pos op e1 e2 => do
    let e1' ← elaborateAllM e1
    let e2' ← elaborateAllM e2
    pure (.binOp pos op e1' e2')
  | .unaryOp pos op e => do
    let e' ← elaborateAllM e
    pure (.unaryOp pos op e')
  | .lam pos param isCov body => do
    let body' ← elaborateAllM body
    pure (.lam pos param isCov body')
  | .app pos fn arg isCov => do
    let fn' ← elaborateAllM fn
    let arg' ← elaborateAllM arg
    pure (.app pos fn' arg' isCov)
  | .let_ pos x ty e1 e2 => do
    let e1' ← elaborateAllM e1
    let e2' ← elaborateAllM e2
    pure (.let_ pos x ty e1' e2')
  | .letRec pos x ty e1 e2 => do
    let e1' ← elaborateAllM e1
    let e2' ← elaborateAllM e2
    pure (.letRec pos x ty e1' e2')
  | .match_ pos e cases => do
    let e' ← elaborateAllM e
    let cases' ← cases.mapM (fun (p, body) => do
      let body' ← elaborateAllM body
      pure (p, body'))
    pure (.match_ pos e' cases')
  | .field pos e f => do
    let e' ← elaborateAllM e
    pure (.field pos e' f)
  | .ann pos e ty => do
    let e' ← elaborateAllM e
    pure (.ann pos e' ty)
  | .record pos fields => do
    let fields' ← fields.mapM (fun (name, expr) => do
      let expr' ← elaborateAllM expr
      pure (name, expr'))
    pure (.record pos fields')
  | .if_ pos c t f => do
    let c' ← elaborateAllM c
    let t' ← elaborateAllM t
    let f' ← elaborateAllM f
    pure (.if_ pos c' t' f')
  | .hash pos => pure (.hash pos)  -- Hash self-reference (passed through)
  | .label pos name body => do
    let body' ← elaborateAllM body
    pure (.label pos name body')
  | .goto pos value continuation => do
    let value' ← elaborateAllM value
    let continuation' ← elaborateAllM continuation
    pure (.goto pos value' continuation')
  | .con pos name args => do
    let args' ← args.mapM elaborateAllM
    pure (.con pos name args')
  | e => pure e  -- Literals and variables

/-- Recursively elaborates all codata expressions found within an expression tree. -/
def elaborateAll (e : Expr) : Except ElaborateError Expr :=
  (elaborateAllM e).run' 0

end Ziku

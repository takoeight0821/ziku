import Ziku.Syntax

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
inductive ElaborateError where
  | mixedAccessors (pos : SourcePos) (msg : String)
  | emptyCopattern (pos : SourcePos)
  | customError (pos : SourcePos) (msg : String)
  deriving Repr, Nonempty

def ElaborateError.toString : ElaborateError → String
  | .mixedAccessors pos msg =>
    s!"Elaboration error at {pos.line}:{pos.col}: {msg}"
  | .emptyCopattern pos =>
    s!"Empty copattern at {pos.line}:{pos.col}"
  | .customError pos msg =>
    s!"Elaboration error at {pos.line}:{pos.col}: {msg}"

instance : ToString ElaborateError := ⟨ElaborateError.toString⟩

-- Classification of copattern accessors
inductive AccessorKind where
  | field : AccessorKind
  | call : AccessorKind
  deriving Repr, BEq, DecidableEq

-- Get the kind of an accessor
def Accessor.kind : Accessor → AccessorKind
  | .field _ => .field
  | .apply _ => .call

-- Clause with pattern guards, copattern, and body
structure Clause where
  patterns : List Pat
  copattern : Copattern
  body : Expr
  deriving Repr, BEq

-- Default position for Inhabited instances (not from user code)
def defaultPos : SourcePos := { line := 0, col := 0 }

-- Make Clause inhabited for head!
instance : Inhabited Clause where
  default := {
    patterns := [],
    copattern := [],
    body := .lit defaultPos .unit
  }

-- Get the kind of the first accessor in a copattern, if any
def Copattern.firstKind? : Copattern → Option AccessorKind
  | [] => none
  | acc :: _ => some acc.kind

-- Check if all copatterns have the same first accessor kind
def allSameKind (clauses : List Clause) : Option AccessorKind :=
  match clauses with
  | [] => none
  | first :: rest =>
    let firstKind := first.copattern.firstKind?
    if rest.all (fun c => c.copattern.firstKind? == firstKind) then
      firstKind
    else
      none

-- Group clauses by their copattern
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
def buildMatchExpr (pos : SourcePos) (argName : Ident) (clauses : List Clause)
    : Except ElaborateError Expr := do
  let cases ← clauses.mapM fun clause =>
    match clause.patterns with
    | [pat] => pure (pat, clause.body)
    | [] => throw (.customError pos "expected pattern in clause")
    | _ => throw (.customError pos "multiple patterns not yet supported")
  pure (.match_ pos (.var pos argName) cases)

-- Inhabited instance for Except ElaborateError Expr
instance : Inhabited (Except ElaborateError Expr) where
  default := throw (.customError defaultPos "uninhabited")

mutual

-- Elaborate pattern guards into lambda + match + codata
-- { pat1 #copat1 => body1, pat2 #copat2 => body2 } becomes:
-- \arg => { copat1 = match arg with | pat1 => body1, copat2 = match arg with | pat2 => body2 }
partial def elaborateWithPatternGuards (pos : SourcePos) (clauses : List Clause)
    : Except ElaborateError Expr := do
  -- Validate: all clauses must have exactly one pattern
  for clause in clauses do
    if clause.patterns.isEmpty then
      throw (.customError pos "mixed pattern guards: some clauses have patterns, some don't")
    if clause.patterns.length > 1 then
      throw (.customError pos "multiple pattern arguments not yet supported")

  -- Generate fresh argument name
  let argName := "_pat_arg"

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
partial def elaboratePatternMatch (pos : SourcePos) (clauses : List Clause) : Except ElaborateError Expr :=
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
partial def elaborate (pos : SourcePos) (rawClauses : List (List Pat × Copattern × Expr)) : Except ElaborateError Expr :=
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
      -- Multi-param copatterns like #(x, y) are desugared to #(x) => { #(y) => ... }
      -- Check first accessor
      match clauses.head? with
      | none => throw (.emptyCopattern pos)
      | some firstClause =>
        match firstClause.copattern with
        | .apply paramName :: _ =>
          -- All clauses should have .apply as first accessor
          -- Group clauses by parameter pattern and create lambda
          let mut lamClauses : List Clause := []

          for clause in clauses do
            match clause.copattern with
            | .apply _ :: restCopat =>
              let newClause : Clause := {
                patterns := clause.patterns,
                copattern := restCopat,
                body := clause.body
              }
              lamClauses := lamClauses ++ [newClause]
            | _ =>
              throw (.customError pos "expected call accessor")

          -- Recursively elaborate the body with remaining copatterns
          let bodyExpr ← elaborate pos (lamClauses.map (fun c => (c.patterns, c.copattern, c.body)))

          -- Create lambda
          pure (.lam pos paramName false bodyExpr)

        | _ => throw (.customError pos "expected call accessor")

end -- mutual

-- Top-level elaboration entry point
def elaborateExpr : Expr → Except ElaborateError Expr
  | .codata pos clauses => elaborate pos clauses
  | e => pure e

-- Recursively elaborate all codata expressions in an expression
partial def elaborateAll : Expr → Except ElaborateError Expr
  | .codata pos clauses => do
    let elaborated ← elaborate pos clauses
    elaborateAll elaborated
  | .binOp pos op e1 e2 => do
    let e1' ← elaborateAll e1
    let e2' ← elaborateAll e2
    pure (.binOp pos op e1' e2')
  | .unaryOp pos op e => do
    let e' ← elaborateAll e
    pure (.unaryOp pos op e')
  | .lam pos param isCov body => do
    let body' ← elaborateAll body
    pure (.lam pos param isCov body')
  | .app pos fn arg isCov => do
    let fn' ← elaborateAll fn
    let arg' ← elaborateAll arg
    pure (.app pos fn' arg' isCov)
  | .let_ pos x ty e1 e2 => do
    let e1' ← elaborateAll e1
    let e2' ← elaborateAll e2
    pure (.let_ pos x ty e1' e2')
  | .letRec pos x ty e1 e2 => do
    let e1' ← elaborateAll e1
    let e2' ← elaborateAll e2
    pure (.letRec pos x ty e1' e2')
  | .match_ pos e cases => do
    let e' ← elaborateAll e
    let cases' ← cases.mapM (fun (p, body) => do
      let body' ← elaborateAll body
      pure (p, body'))
    pure (.match_ pos e' cases')
  | .field pos e f => do
    let e' ← elaborateAll e
    pure (.field pos e' f)
  | .ann pos e ty => do
    let e' ← elaborateAll e
    pure (.ann pos e' ty)
  | .record pos fields => do
    let fields' ← fields.mapM (fun (name, expr) => do
      let expr' ← elaborateAll expr
      pure (name, expr'))
    pure (.record pos fields')
  | .if_ pos c t f => do
    let c' ← elaborateAll c
    let t' ← elaborateAll t
    let f' ← elaborateAll f
    pure (.if_ pos c' t' f')
  | .cut pos e1 e2 => do
    let e1' ← elaborateAll e1
    let e2' ← elaborateAll e2
    pure (.cut pos e1' e2')
  | .mu pos x body => do
    let body' ← elaborateAll body
    pure (.mu pos x body')
  | .hash pos => pure (.hash pos)  -- Hash self-reference (passed through)
  | .label pos name body => do
    let body' ← elaborateAll body
    pure (.label pos name body')
  | .goto pos value continuation => do
    let value' ← elaborateAll value
    let continuation' ← elaborateAll continuation
    pure (.goto pos value' continuation')
  | .con pos name args => do
    let args' ← args.mapM elaborateAll
    pure (.con pos name args')
  | e => pure e  -- Literals and variables

end Ziku

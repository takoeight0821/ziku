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

-- Make Clause inhabited for head!
instance : Inhabited Clause where
  default := {
    patterns := [],
    copattern := [],
    body := .lit { line := 0, col := 0 } .unit
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

-- Elaborate pattern guards into a match expression
def elaboratePatternMatch (pos : SourcePos) (clauses : List Clause) : Except ElaborateError Expr :=
  if clauses.isEmpty then
    throw (.emptyCopattern pos)
  else if clauses.length == 1 && clauses.head!.patterns.isEmpty then
    -- Single clause with no patterns, just return the body
    pure clauses.head!.body
  else
    throw (.customError pos "pattern guards not yet implemented")

-- Inhabited instance for Except ElaborateError Expr
instance : Inhabited (Except ElaborateError Expr) where
  default := throw (.customError { line := 0, col := 0 } "uninhabited")

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
          pure (.lam pos paramName bodyExpr)

        | _ => throw (.customError pos "expected call accessor")

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
  | .lam pos param body => do
    let body' ← elaborateAll body
    pure (.lam pos param body')
  | .app pos fn arg => do
    let fn' ← elaborateAll fn
    let arg' ← elaborateAll arg
    pure (.app pos fn' arg')
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
  | .mu pos x e => do
    let e' ← elaborateAll e
    pure (.mu pos x e')
  | .hash pos => pure (.hash pos)  -- Hash self-reference (passed through)
  | e => pure e  -- Literals and variables

end Ziku

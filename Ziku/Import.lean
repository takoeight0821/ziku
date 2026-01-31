import Ziku.Syntax
import Ziku.Parser
import Ziku.Path

/-!
# Import Resolution

Functions for collecting and resolving import expressions in Ziku code.
This module provides shared utilities used by both the compiler (Main.lean) and test runner.
-/

namespace Ziku.Import

open Ziku (Expr Pat Copattern Ident Ty parse parseSignature)

/-- Type alias for import type mappings (path -> type) -/
abbrev ImportTypeMap := List (String × Ty)

/-- Collect all import paths from an expression -/
partial def collectImports : Expr → List String
  | .import_ _ path => [path]
  | .binOp _ _ e1 e2 => collectImports e1 ++ collectImports e2
  | .unaryOp _ _ e => collectImports e
  | .lam _ _ _ body => collectImports body
  | .app _ fn arg _ => collectImports fn ++ collectImports arg
  | .let_ _ _ _ e1 e2 => collectImports e1 ++ collectImports e2
  | .letRec _ _ _ e1 e2 => collectImports e1 ++ collectImports e2
  | .match_ _ scrutinee cases =>
    collectImports scrutinee ++ (cases.flatMap fun (_, body) => collectImports body)
  | .codata _ clauses =>
    clauses.flatMap fun (_, _, body) => collectImports body
  | .field _ e _ => collectImports e
  | .ann _ e _ => collectImports e
  | .record _ fields =>
    fields.flatMap fun (_, e) => collectImports e
  | .if_ _ c t f => collectImports c ++ collectImports t ++ collectImports f
  | .label _ _ body => collectImports body
  | .goto _ e1 e2 => collectImports e1 ++ collectImports e2
  | .con _ _ args => args.flatMap collectImports
  | _ => []

/-- Resolve import types by loading signature files.
    Returns an ImportTypeMap mapping paths to their types. -/
def resolveImportTypes (basePath : System.FilePath) (imports : List String)
    : IO (Except String ImportTypeMap) := do
  let ctx := Ziku.Path.contextFromFile basePath
  let mut result : ImportTypeMap := []

  for importPath in imports.eraseDups do
    -- Resolve the import path
    match ← Ziku.Path.resolve ctx importPath with
    | .notFound tried =>
      return .error s!"Import file not found: {importPath}\nTried: {tried}"
    | .found resolvedPath =>
      -- Get the signature file path
      let sigPath := Ziku.Path.toSignaturePath resolvedPath
      -- Check if signature file exists
      if ← sigPath.pathExists then
        let sigContent ← IO.FS.readFile sigPath
        match parseSignature sigContent with
        | .error msg =>
          return .error s!"Failed to parse signature {sigPath}: {msg}"
        | .ok ty =>
          result := (importPath, ty) :: result
      else
        return .error s!"Signature file not found: {sigPath}\nEvery imported .ziku file must have a corresponding .ziki signature file."

  return .ok result

/-- Expand import expressions by reading and parsing imported files.
    Tracks visited paths to detect circular imports.
    Returns the expanded expression with imports replaced by their evaluated content. -/
partial def expandImports (basePath : System.FilePath) (expr : Expr)
    (visited : List String := []) : IO (Except String Expr) := do
  match expr with
  | .import_ pos path =>
    -- Resolve the import path
    let ctx := Ziku.Path.contextFromFile basePath
    match ← Ziku.Path.resolve ctx path with
    | .notFound tried =>
      return .error s!"Import file not found: {path}\nTried: {tried}"
    | .found resolvedPath =>
      -- Check for circular import
      let resolvedStr := resolvedPath.toString
      if visited.contains resolvedStr then
        return .error s!"Circular import detected: {path}\nImport chain: {visited.reverse.append [resolvedStr]}"
      -- Read and parse the imported file
      let content ← IO.FS.readFile resolvedPath
      match parse content with
      | .error msg =>
        return .error s!"Failed to parse {resolvedPath}: {msg}"
      | .ok importedExpr =>
        -- Recursively expand imports in the imported expression
        expandImports resolvedPath importedExpr (resolvedStr :: visited)
  | .binOp p op e1 e2 => do
    let e1' ← expandImports basePath e1 visited
    let e2' ← expandImports basePath e2 visited
    match e1', e2' with
    | .ok e1'', .ok e2'' => return .ok (.binOp p op e1'' e2'')
    | .error msg, _ => return .error msg
    | _, .error msg => return .error msg
  | .unaryOp p op e => do
    let e' ← expandImports basePath e visited
    match e' with
    | .ok e'' => return .ok (.unaryOp p op e'')
    | .error msg => return .error msg
  | .lam p param isCov body => do
    let body' ← expandImports basePath body visited
    match body' with
    | .ok body'' => return .ok (.lam p param isCov body'')
    | .error msg => return .error msg
  | .app p fn arg isCov => do
    let fn' ← expandImports basePath fn visited
    let arg' ← expandImports basePath arg visited
    match fn', arg' with
    | .ok fn'', .ok arg'' => return .ok (.app p fn'' arg'' isCov)
    | .error msg, _ => return .error msg
    | _, .error msg => return .error msg
  | .let_ p x ty e1 e2 => do
    let e1' ← expandImports basePath e1 visited
    let e2' ← expandImports basePath e2 visited
    match e1', e2' with
    | .ok e1'', .ok e2'' => return .ok (.let_ p x ty e1'' e2'')
    | .error msg, _ => return .error msg
    | _, .error msg => return .error msg
  | .letRec p x ty e1 e2 => do
    let e1' ← expandImports basePath e1 visited
    let e2' ← expandImports basePath e2 visited
    match e1', e2' with
    | .ok e1'', .ok e2'' => return .ok (.letRec p x ty e1'' e2'')
    | .error msg, _ => return .error msg
    | _, .error msg => return .error msg
  | .match_ p scrutinee cases => do
    let scrutinee' ← expandImports basePath scrutinee visited
    match scrutinee' with
    | .error msg => return .error msg
    | .ok scrutinee'' =>
      let mut newCases : List (Pat × Expr) := []
      for (pat, body) in cases do
        let body' ← expandImports basePath body visited
        match body' with
        | .error msg => return .error msg
        | .ok body'' => newCases := newCases ++ [(pat, body'')]
      return .ok (.match_ p scrutinee'' newCases)
  | .codata p clauses => do
    let mut newClauses : List (List Pat × Copattern × Expr) := []
    for (pats, copat, body) in clauses do
      let body' ← expandImports basePath body visited
      match body' with
      | .error msg => return .error msg
      | .ok body'' => newClauses := newClauses ++ [(pats, copat, body'')]
    return .ok (.codata p newClauses)
  | .field p e f => do
    let e' ← expandImports basePath e visited
    match e' with
    | .ok e'' => return .ok (.field p e'' f)
    | .error msg => return .error msg
  | .ann p e ty => do
    let e' ← expandImports basePath e visited
    match e' with
    | .ok e'' => return .ok (.ann p e'' ty)
    | .error msg => return .error msg
  | .record p fields => do
    let mut newFields : List (Ident × Expr) := []
    for (name, e) in fields do
      let e' ← expandImports basePath e visited
      match e' with
      | .error msg => return .error msg
      | .ok e'' => newFields := newFields ++ [(name, e'')]
    return .ok (.record p newFields)
  | .if_ p c t f => do
    let c' ← expandImports basePath c visited
    let t' ← expandImports basePath t visited
    let f' ← expandImports basePath f visited
    match c', t', f' with
    | .ok c'', .ok t'', .ok f'' => return .ok (.if_ p c'' t'' f'')
    | .error msg, _, _ => return .error msg
    | _, .error msg, _ => return .error msg
    | _, _, .error msg => return .error msg
  | .label p name body => do
    let body' ← expandImports basePath body visited
    match body' with
    | .ok body'' => return .ok (.label p name body'')
    | .error msg => return .error msg
  | .goto p e1 e2 => do
    let e1' ← expandImports basePath e1 visited
    let e2' ← expandImports basePath e2 visited
    match e1', e2' with
    | .ok e1'', .ok e2'' => return .ok (.goto p e1'' e2'')
    | .error msg, _ => return .error msg
    | _, .error msg => return .error msg
  | .con p name args => do
    let mut newArgs : List Expr := []
    for arg in args do
      let arg' ← expandImports basePath arg visited
      match arg' with
      | .error msg => return .error msg
      | .ok arg'' => newArgs := newArgs ++ [arg'']
    return .ok (.con p name newArgs)
  | other => return .ok other  -- Literals, variables, hash, extern

end Ziku.Import

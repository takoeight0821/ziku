import Ziku.Syntax
import Ziku.Parser
import Ziku.Path

/-!
# Import Resolution

Functions for collecting and resolving import expressions in Ziku code.
This module provides shared utilities used by both the compiler (Main.lean) and test runner.
-/

namespace Ziku.Import

open Ziku (Expr Pat Copattern Ident Ty ImportTypeMap parse parseSignature)

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

private def resolveImportPath (basePath : System.FilePath) (importPath : String)
    : ExceptT String IO System.FilePath := do
  let ctx := Ziku.Path.contextFromFile basePath
  match ← Ziku.Path.resolve ctx importPath with
  | .notFound tried =>
    throw s!"Import file not found: {importPath}\nTried: {tried}"
  | .found resolvedPath =>
    return resolvedPath

/-- Resolve import types by loading signature files.
    Returns an ImportTypeMap mapping paths to their types. -/
def resolveImportTypes (basePath : System.FilePath) (imports : List String)
    : ExceptT String IO ImportTypeMap := do
  let mut result : ImportTypeMap := []

  for importPath in imports.eraseDups do
    let resolvedPath ← resolveImportPath basePath importPath
    let sigPath := Ziku.Path.toSignaturePath resolvedPath
    if ← sigPath.pathExists then
      let sigContent ← IO.FS.readFile sigPath
      match parseSignature sigContent with
      | .error msg =>
        throw s!"Failed to parse signature {sigPath}: {msg}"
      | .ok ty =>
        result := (importPath, ty) :: result
    else
      throw s!"Signature file not found: {sigPath}\nEvery imported .ziku file must have a corresponding .ziki signature file."

  return result

/-- Expand import expressions by reading and parsing imported files.
    Tracks visited paths to detect circular imports.
    Returns the expanded expression with imports replaced by their evaluated content. -/
partial def expandImports (basePath : System.FilePath) (expr : Expr)
    (visited : List String := []) : ExceptT String IO Expr := do
  match expr with
  | .import_ _pos path =>
    let resolvedPath ← resolveImportPath basePath path
    let resolvedStr := resolvedPath.toString
    if visited.contains resolvedStr then
      throw s!"Circular import detected: {path}\nImport chain: {visited.reverse.append [resolvedStr]}"
    let content ← IO.FS.readFile resolvedPath
    match parse content with
    | .error msg =>
      throw s!"Failed to parse {resolvedPath}: {msg}"
    | .ok importedExpr =>
      expandImports resolvedPath importedExpr (resolvedStr :: visited)
  | .binOp p op e1 e2 =>
    return .binOp p op (← expandImports basePath e1 visited) (← expandImports basePath e2 visited)
  | .unaryOp p op e =>
    return .unaryOp p op (← expandImports basePath e visited)
  | .lam p param isCov body =>
    return .lam p param isCov (← expandImports basePath body visited)
  | .app p fn arg isCov =>
    return .app p (← expandImports basePath fn visited) (← expandImports basePath arg visited) isCov
  | .let_ p x ty e1 e2 =>
    return .let_ p x ty (← expandImports basePath e1 visited) (← expandImports basePath e2 visited)
  | .letRec p x ty e1 e2 =>
    return .letRec p x ty (← expandImports basePath e1 visited) (← expandImports basePath e2 visited)
  | .match_ p scrutinee cases =>
    let scrutinee' ← expandImports basePath scrutinee visited
    let cases' ← cases.mapM fun (pat, body) => do
      return (pat, ← expandImports basePath body visited)
    return .match_ p scrutinee' cases'
  | .codata p clauses =>
    let clauses' ← clauses.mapM fun (pats, copat, body) => do
      return (pats, copat, ← expandImports basePath body visited)
    return .codata p clauses'
  | .field p e f =>
    return .field p (← expandImports basePath e visited) f
  | .ann p e ty =>
    return .ann p (← expandImports basePath e visited) ty
  | .record p fields =>
    let fields' ← fields.mapM fun (name, e) => do
      return (name, ← expandImports basePath e visited)
    return .record p fields'
  | .if_ p c t f =>
    return .if_ p (← expandImports basePath c visited) (← expandImports basePath t visited) (← expandImports basePath f visited)
  | .label p name body =>
    return .label p name (← expandImports basePath body visited)
  | .goto p e1 e2 =>
    return .goto p (← expandImports basePath e1 visited) (← expandImports basePath e2 visited)
  | .con p name args =>
    let args' ← args.mapM fun arg => expandImports basePath arg visited
    return .con p name args'
  | other => return other  -- Literals, variables, hash, extern

end Ziku.Import

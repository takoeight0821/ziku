import Ziku

open Ziku

/-!
# Import Resolution

Functions for collecting and resolving import expressions in Ziku code.
-/

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
    Returns the expanded expression with imports replaced by their evaluated content. -/
partial def expandImports (basePath : System.FilePath) (expr : Expr) : IO (Except String Expr) := do
  match expr with
  | .import_ pos path =>
    -- Resolve the import path
    let ctx := Ziku.Path.contextFromFile basePath
    match ← Ziku.Path.resolve ctx path with
    | .notFound tried =>
      return .error s!"Import file not found: {path}\nTried: {tried}"
    | .found resolvedPath =>
      -- Read and parse the imported file
      let content ← IO.FS.readFile resolvedPath
      match parse content with
      | .error msg =>
        return .error s!"Failed to parse {resolvedPath}: {msg}"
      | .ok importedExpr =>
        -- Recursively expand imports in the imported expression
        expandImports resolvedPath importedExpr
  | .binOp p op e1 e2 => do
    let e1' ← expandImports basePath e1
    let e2' ← expandImports basePath e2
    match e1', e2' with
    | .ok e1'', .ok e2'' => return .ok (.binOp p op e1'' e2'')
    | .error msg, _ => return .error msg
    | _, .error msg => return .error msg
  | .unaryOp p op e => do
    let e' ← expandImports basePath e
    match e' with
    | .ok e'' => return .ok (.unaryOp p op e'')
    | .error msg => return .error msg
  | .lam p param isCov body => do
    let body' ← expandImports basePath body
    match body' with
    | .ok body'' => return .ok (.lam p param isCov body'')
    | .error msg => return .error msg
  | .app p fn arg isCov => do
    let fn' ← expandImports basePath fn
    let arg' ← expandImports basePath arg
    match fn', arg' with
    | .ok fn'', .ok arg'' => return .ok (.app p fn'' arg'' isCov)
    | .error msg, _ => return .error msg
    | _, .error msg => return .error msg
  | .let_ p x ty e1 e2 => do
    let e1' ← expandImports basePath e1
    let e2' ← expandImports basePath e2
    match e1', e2' with
    | .ok e1'', .ok e2'' => return .ok (.let_ p x ty e1'' e2'')
    | .error msg, _ => return .error msg
    | _, .error msg => return .error msg
  | .letRec p x ty e1 e2 => do
    let e1' ← expandImports basePath e1
    let e2' ← expandImports basePath e2
    match e1', e2' with
    | .ok e1'', .ok e2'' => return .ok (.letRec p x ty e1'' e2'')
    | .error msg, _ => return .error msg
    | _, .error msg => return .error msg
  | .match_ p scrutinee cases => do
    let scrutinee' ← expandImports basePath scrutinee
    match scrutinee' with
    | .error msg => return .error msg
    | .ok scrutinee'' =>
      let mut newCases : List (Pat × Expr) := []
      for (pat, body) in cases do
        let body' ← expandImports basePath body
        match body' with
        | .error msg => return .error msg
        | .ok body'' => newCases := newCases ++ [(pat, body'')]
      return .ok (.match_ p scrutinee'' newCases)
  | .codata p clauses => do
    let mut newClauses : List (List Pat × Copattern × Expr) := []
    for (pats, copat, body) in clauses do
      let body' ← expandImports basePath body
      match body' with
      | .error msg => return .error msg
      | .ok body'' => newClauses := newClauses ++ [(pats, copat, body'')]
    return .ok (.codata p newClauses)
  | .field p e f => do
    let e' ← expandImports basePath e
    match e' with
    | .ok e'' => return .ok (.field p e'' f)
    | .error msg => return .error msg
  | .ann p e ty => do
    let e' ← expandImports basePath e
    match e' with
    | .ok e'' => return .ok (.ann p e'' ty)
    | .error msg => return .error msg
  | .record p fields => do
    let mut newFields : List (Ident × Expr) := []
    for (name, e) in fields do
      let e' ← expandImports basePath e
      match e' with
      | .error msg => return .error msg
      | .ok e'' => newFields := newFields ++ [(name, e'')]
    return .ok (.record p newFields)
  | .if_ p c t f => do
    let c' ← expandImports basePath c
    let t' ← expandImports basePath t
    let f' ← expandImports basePath f
    match c', t', f' with
    | .ok c'', .ok t'', .ok f'' => return .ok (.if_ p c'' t'' f'')
    | .error msg, _, _ => return .error msg
    | _, .error msg, _ => return .error msg
    | _, _, .error msg => return .error msg
  | .label p name body => do
    let body' ← expandImports basePath body
    match body' with
    | .ok body'' => return .ok (.label p name body'')
    | .error msg => return .error msg
  | .goto p e1 e2 => do
    let e1' ← expandImports basePath e1
    let e2' ← expandImports basePath e2
    match e1', e2' with
    | .ok e1'', .ok e2'' => return .ok (.goto p e1'' e2'')
    | .error msg, _ => return .error msg
    | _, .error msg => return .error msg
  | .con p name args => do
    let mut newArgs : List Expr := []
    for arg in args do
      let arg' ← expandImports basePath arg
      match arg' with
      | .error msg => return .error msg
      | .ok arg'' => newArgs := newArgs ++ [arg'']
    return .ok (.con p name newArgs)
  | other => return .ok other  -- Literals, variables, hash, extern

/-- Execution mode for the Ziku compiler. -/
inductive Mode
  /-- Run the REPL. -/
  | repl (bigStep : Bool)
  /-- Parse the input and print the AST. -/
  | parse
  /-- Infer the type of the input. -/
  | infer
  /-- Translate the input to IR and print it. -/
  | translate
  /-- Compile the input to Scheme. -/
  | scheme
  /-- Evaluate the input using the small-step evaluator. -/
  | eval
  /-- Evaluate the input using the big-step evaluator. -/
  | evalBigStep

/-- Parses command line arguments to determine the execution mode. -/
def parseArgs (args : List String) : Mode :=
  match args with
  | "--parse" :: _ => .parse
  | "--infer" :: _ => .infer
  | "--translate" :: _ => .translate
  | "--scheme" :: _ => .scheme
  | "--eval" :: "--big-step" :: _ => .evalBigStep
  | "--big-step" :: "--eval" :: _ => .evalBigStep
  | "--eval" :: _ => .eval
  | "--big-step" :: _ => 
    -- If there's a file argument after --big-step, it's eval. Otherwise repl.
    if args.length > 1 && !args[1]!.startsWith "-" then .evalBigStep
    else .repl true
  | [] => .repl false
  | _ => .repl false

/-- Runs the compiler on a given input string using the specified mode.
    basePath is the path of the source file (used for resolving relative imports). -/
def runOnInput (mode : Mode) (input : String) (basePath : System.FilePath := ".") : IO Unit := do
  match parse input with
  | .error msg =>
    IO.eprintln s!"Parse error: {msg}"
    IO.Process.exit 1
  | .ok expr =>
    -- Collect and resolve imports
    let imports := collectImports expr
    let importTypes ← if imports.isEmpty then pure (.ok []) else resolveImportTypes basePath imports

    match importTypes with
    | .error msg =>
      IO.eprintln s!"Import error: {msg}"
      IO.Process.exit 1
    | .ok importTypeMap =>
      match mode with
      | .parse =>
        IO.println s!"{repr expr}"
      | .infer =>
        match runInfer expr [] importTypeMap with
        | .error err =>
          IO.eprintln s!"Type error: {err}"
          IO.Process.exit 1
        | .ok (ty, _) =>
          IO.println s!"{ty}"
      | .translate =>
        -- Expand imports before translation
        let expanded ← expandImports basePath expr
        match expanded with
        | .error msg =>
          IO.eprintln s!"Import expansion error: {msg}"
          IO.Process.exit 1
        | .ok expr' =>
          match Translate.translateToStatement expr' with
          | .error err =>
            IO.eprintln s!"Translate error: {err}"
            IO.Process.exit 1
          | .ok stmt =>
            IO.println s!"{stmt}"
      | .scheme =>
        -- Expand imports before compilation
        let expanded ← expandImports basePath expr
        match expanded with
        | .error msg =>
          IO.eprintln s!"Import expansion error: {msg}"
          IO.Process.exit 1
        | .ok expr' =>
          match Translate.translateToStatement expr' with
          | .error err =>
            IO.eprintln s!"Translate error: {err}"
            IO.Process.exit 1
          | .ok stmt =>
            let scheme := Backend.Scheme.compile stmt
            IO.println scheme
      | .eval | .repl false =>
        -- Expand imports before evaluation
        let expanded ← expandImports basePath expr
        match expanded with
        | .error msg =>
          IO.eprintln s!"Import expansion error: {msg}"
          IO.Process.exit 1
        | .ok expr' =>
          match Translate.translateToStatement expr' with
          | .error err =>
            IO.eprintln s!"Translate error: {err}"
            IO.Process.exit 1
          | .ok stmt =>
            match ← IR.eval stmt with
            | .value p _ => IO.println s!"{p}"
            | .stuck s _ =>
              IO.eprintln s!"Stuck: {s}"
              IO.Process.exit 1
            | .error msg =>
              IO.eprintln s!"Eval error: {msg}"
              IO.Process.exit 1
      | .evalBigStep | .repl true =>
        -- Expand imports before evaluation
        let expanded ← expandImports basePath expr
        match expanded with
        | .error msg =>
          IO.eprintln s!"Import expansion error: {msg}"
          IO.Process.exit 1
        | .ok expr' =>
          match Translate.translateToStatement expr' with
          | .error err =>
            IO.eprintln s!"Translate error: {err}"
            IO.Process.exit 1
          | .ok stmt =>
            match ← IR.BigStepEval.eval stmt with
            | .value v => IO.println s!"{v}"
            | .error msg =>
              IO.eprintln s!"Eval error: {msg}"
              IO.Process.exit 1

/-- Starts an interactive REPL loop. -/
partial def repl (useBigStep : Bool) : IO Unit := do
  IO.print "> "
  let stdout ← IO.getStdout
  stdout.flush
  let stdin ← IO.getStdin
  let input ← stdin.getLine
  let input := input.trimAscii.toString

  -- Handle EOF or quit commands
  if input.isEmpty then
    IO.println "\nGoodbye!"
    return

  if input == ":quit" || input == ":q" then
    IO.println "Goodbye!"
    return

  match parse input with
  | .error msg =>
    IO.println s!"Parse error: {msg}"
    repl useBigStep
  | .ok expr =>
    match Translate.translateToStatement expr with
    | .error err =>
      IO.println s!"Translate error: {err}"
      repl useBigStep
    | .ok stmt =>
      if useBigStep then
        match ← IR.BigStepEval.eval stmt with
        | .value v => IO.println s!"{v}"
        | .error msg => IO.println s!"Eval error: {msg}"
      else
        match ← IR.eval stmt with
        | .value p _ => IO.println s!"{p}"
        | .stuck s _ => IO.println s!"Stuck: {s}"
        | .error msg => IO.println s!"Eval error: {msg}"
      repl useBigStep

/-- Extract file path from command line arguments -/
def getFilePath (args : List String) : Option String :=
  match args with
  | "--eval" :: "--big-step" :: file :: _ => some file
  | "--big-step" :: "--eval" :: file :: _ => some file
  | "--eval" :: file :: _ => if file.startsWith "-" then none else some file
  | "--big-step" :: file :: _ => if file.startsWith "-" then none else some file
  | "--scheme" :: file :: _ => some file
  | "--parse" :: file :: _ => some file
  | "--infer" :: file :: _ => some file
  | "--translate" :: file :: _ => some file
  | _ => none

/-- Main entry point for the Ziku compiler. -/
def main (args : List String) : IO Unit := do
  let mode := parseArgs args
  match mode with
  | .repl bigStep =>
    IO.println s!"Ziku REPL ({if bigStep then "Big-Step" else "Small-Step"})"
    IO.println "Type :quit or :q to exit"
    repl bigStep
  | _ =>
    let (input, basePath) ← match getFilePath args with
      | some file =>
        let content ← IO.FS.readFile file
        pure (content, System.FilePath.mk file)
      | none =>
        let content ← (← IO.getStdin).readToEnd
        pure (content, System.FilePath.mk ".")
    runOnInput mode input.trimAscii.toString basePath

import Ziku

open Ziku
open Ziku.Import

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
    let importTypes ← if imports.isEmpty then pure (.ok []) else (resolveImportTypes basePath imports).run

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
      | _ =>
        -- All remaining modes need import expansion + translation
        match ← (expandImports basePath expr).run with
        | .error msg =>
          IO.eprintln s!"Import expansion error: {msg}"
          IO.Process.exit 1
        | .ok expanded =>
          match elaborateAll expanded with
          | .error err =>
            IO.eprintln s!"Elaboration error: {err}"
            IO.Process.exit 1
          | .ok elaborated =>
          match Translate.translateToStatement elaborated with
          | .error err =>
            IO.eprintln s!"Translate error: {err}"
            IO.Process.exit 1
          | .ok stmt =>
            match mode with
            | .translate => IO.println s!"{stmt}"
            | .scheme => IO.println (Backend.Scheme.compile stmt)
            | .eval | .repl false =>
              match ← IR.eval stmt with
              | .value p _ => IO.println s!"{p}"
              | .stuck s _ =>
                IO.eprintln s!"Stuck: {s}"
                IO.Process.exit 1
              | .error msg =>
                IO.eprintln s!"Eval error: {msg}"
                IO.Process.exit 1
            | .evalBigStep | .repl true =>
              match ← IR.BigStepEval.eval stmt with
              | .value v => IO.println s!"{v}"
              | .error msg =>
                IO.eprintln s!"Eval error: {msg}"
                IO.Process.exit 1
            | .parse | .infer => pure ()  -- unreachable

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
    match elaborateAll expr with
    | .error err =>
      IO.println s!"Elaboration error: {err}"
      repl useBigStep
    | .ok elaborated =>
    match Translate.translateToStatement elaborated with
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

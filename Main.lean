import Ziku

open Ziku

inductive Mode
  | repl (bigStep : Bool)
  | parse
  | infer
  | translate
  | scheme
  | eval
  | evalBigStep

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

def runOnInput (mode : Mode) (input : String) : IO Unit := do
  match parse input with
  | .error msg =>
    IO.eprintln s!"Parse error: {msg}"
    IO.Process.exit 1
  | .ok expr =>
    match mode with
    | .parse =>
      IO.println s!"{repr expr}"
    | .infer =>
      match runInfer expr with
      | .error err =>
        IO.eprintln s!"Type error: {err}"
        IO.Process.exit 1
      | .ok (ty, _) =>
        IO.println s!"{ty}"
    | .translate =>
      match Translate.translateToStatement expr with
      | .error err =>
        IO.eprintln s!"Translate error: {err}"
        IO.Process.exit 1
      | .ok stmt =>
        IO.println s!"{stmt}"
    | .scheme =>
      match Translate.translateToStatement expr with
      | .error err =>
        IO.eprintln s!"Translate error: {err}"
        IO.Process.exit 1
      | .ok stmt =>
        let scheme := Backend.Scheme.compile stmt
        IO.println scheme
    | .eval | .repl false =>
      match Translate.translateToStatement expr with
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
      match Translate.translateToStatement expr with
      | .error err =>
        IO.eprintln s!"Translate error: {err}"
        IO.Process.exit 1
      | .ok stmt =>
        match ← IR.BigStepEval.eval stmt with
        | .value v => IO.println s!"{v}"
        | .error msg =>
          IO.eprintln s!"Eval error: {msg}"
          IO.Process.exit 1

partial def repl (useBigStep : Bool) : IO Unit := do
  IO.print "> "
  let stdout ← IO.getStdout
  stdout.flush
  let stdin ← IO.getStdin
  let input ← stdin.getLine
  let input := input.trim

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

def main (args : List String) : IO Unit := do
  let mode := parseArgs args
  match mode with
  | .repl bigStep =>
    IO.println s!"Ziku REPL ({if bigStep then "Big-Step" else "Small-Step"})"
    IO.println "Type :quit or :q to exit"
    repl bigStep
  | _ =>
    let input ← match args with
      | "--eval" :: "--big-step" :: file :: _ => IO.FS.readFile file
      | "--big-step" :: "--eval" :: file :: _ => IO.FS.readFile file
      | "--eval" :: file :: _ => IO.FS.readFile file
      | "--big-step" :: file :: _ => IO.FS.readFile file
      | [_] => (← IO.getStdin).readToEnd
      | _ => (← IO.getStdin).readToEnd
    runOnInput mode input.trim

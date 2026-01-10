import Ziku

open Ziku

inductive Mode
  | repl
  | parse
  | infer
  | translate
  | scheme
  | eval

def parseArgs (args : List String) : Mode :=
  match args with
  | "--parse" :: _ => .parse
  | "--infer" :: _ => .infer
  | "--translate" :: _ => .translate
  | "--scheme" :: _ => .scheme
  | "--eval" :: _ => .eval
  | [] => .repl
  | _ => .repl

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
    | .eval | .repl =>
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

partial def repl : IO Unit := do
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
    repl
  | .ok expr =>
    match Translate.translateToStatement expr with
    | .error err =>
      IO.println s!"Translate error: {err}"
      repl
    | .ok stmt =>
      match ← IR.eval stmt with
      | .value p _ => IO.println s!"{p}"
      | .stuck s _ => IO.println s!"Stuck: {s}"
      | .error msg => IO.println s!"Eval error: {msg}"
      repl

def main (args : List String) : IO Unit := do
  let mode := parseArgs args
  match mode with
  | .repl =>
    IO.println "Ziku REPL"
    IO.println "Type :quit or :q to exit"
    repl
  | _ =>

    let input ← match args with
      | [_, file] => IO.FS.readFile file
      | [_] => (← IO.getStdin).readToEnd
      | _ => return -- Should be handled by repl mode, but here we are in other modes
    runOnInput mode input.trim

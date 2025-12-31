import Ziku.Parser
import Ziku.Elaborate
import Ziku.Translate
import Ziku.Backend.Scheme

open Ziku
open Ziku.Translate
open Ziku.Backend.Scheme

def compileToScheme (input : String) : IO Unit := do
  let input := input.trim
  if input.isEmpty then
    IO.eprintln "Error: Empty input"
    return

  -- Parse
  match parseExprString input with
  | .error msg =>
    IO.eprintln s!"Parse error: {msg}"
  | .ok expr =>
    -- Elaborate codata
    match elaborateAll expr with
    | .error e =>
      IO.eprintln s!"Elaboration error: {e}"
    | .ok elaborated =>
      -- Translate to IR
      match translate elaborated with
      | .error e =>
        IO.eprintln s!"Translation error: {e}"
      | .ok producer =>
        -- Compile to Scheme
        let schemeCode := compileProducer producer
        IO.print schemeCode

def main (args : List String) : IO UInt32 := do
  match args with
  | [] =>
    -- Read from stdin
    let stdin ← IO.getStdin
    let input ← stdin.readToEnd
    compileToScheme input
    return 0
  | ["-h"] | ["--help"] =>
    IO.println "Usage: scheme-backend [OPTIONS] [FILE]"
    IO.println ""
    IO.println "Compile Ziku source to Chez Scheme"
    IO.println ""
    IO.println "Options:"
    IO.println "  -h, --help     Show this help message"
    IO.println "  -e EXPR        Compile expression directly"
    IO.println ""
    IO.println "If no FILE is given, reads from stdin."
    return 0
  | ["-e", expr] =>
    compileToScheme expr
    return 0
  | [filename] =>
    -- Read from file
    let input ← IO.FS.readFile filename
    compileToScheme input
    return 0
  | _ =>
    IO.eprintln "Error: Invalid arguments. Use --help for usage."
    return 1

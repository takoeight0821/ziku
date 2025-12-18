import Ziku

open Ziku

partial def repl (env : Env) : IO Unit := do
  IO.print "> "
  let input ← IO.getStdin >>= (·.getLine)
  let input := input.trim

  if input == ":quit" || input == ":q" then
    IO.println "Goodbye!"
    return

  match parse input with
  | .error msg =>
    IO.println s!"Error: {msg}"
    repl env
  | .ok expr =>
    match eval env expr with
    | none =>
      IO.println "Evaluation error"
      repl env
    | some result =>
      IO.println s!"{result}"
      repl env

def main : IO Unit := do
  IO.println "Ziku REPL"
  IO.println "Type :quit or :q to exit"
  repl []

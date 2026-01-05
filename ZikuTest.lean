import Ziku.Parser
import Ziku.Infer
import Ziku.Elaborate
import Ziku.Translate
import Ziku.IR.Eval
import Ziku.Backend.Scheme

/-- Run a specific phase on input -/
def runPhase (phase : String) (input : String) : IO Unit := do
  match Ziku.parseExprString input.trim with
  | .error e =>
    IO.println s!"Parse error: {e}"
    return
  | .ok expr =>
    match phase with
    | "parse" =>
      IO.println (toString expr)
    | "infer" =>
      match Ziku.runInfer expr with
      | .ok (ty, _) => IO.println (toString ty)
      | .error e => IO.println s!"Type error: {e}"
    | "eval" =>
      match Ziku.elaborateAll expr with
      | .error e =>
        IO.println s!"Elaboration error: {e}"
      | .ok elaborated =>
        match Ziku.Translate.translateToStatement elaborated with
        | .error e =>
          IO.println s!"Translation error: {e}"
        | .ok stmt =>
          let result := Ziku.IR.eval stmt
          match result with
          | .value p => IO.println (Ziku.IR.truncate p.toString)
          | .stuck s => IO.println s!"Stuck: {s}"
          | .error msg => IO.println s!"Runtime error: {msg}"
    | "translate" =>
      match Ziku.elaborateAll expr with
      | .error e =>
        IO.println s!"Elaboration error: {e}"
      | .ok elaborated =>
        match Ziku.Translate.translate elaborated with
        | .error e => IO.println s!"Translation error: {e}"
        | .ok producer => IO.println producer.toString
    | "scheme" =>
      match Ziku.elaborateAll expr with
      | .error e =>
        IO.println s!"Elaboration error: {e}"
      | .ok elaborated =>
        match Ziku.Translate.translate elaborated with
        | .error e => IO.println s!"Translation error: {e}"
        | .ok producer =>
          IO.println (Ziku.Backend.Scheme.compileProducer producer)
    | _ =>
      IO.println s!"Unknown phase: {phase}"
      IO.println "Valid phases: parse, infer, eval, translate, scheme"

def main (args : List String) : IO Unit := do
  match args with
  | [phase, input] =>
    -- Check if input is a file path
    if (← System.FilePath.pathExists input) then
      let content ← IO.FS.readFile input
      runPhase phase content
    else
      runPhase phase input
  | [phase] =>
    -- Read from stdin
    let stdin ← IO.getStdin
    let input ← stdin.readToEnd
    runPhase phase input
  | _ =>
    IO.println "Usage: ziku-test <phase> [expression-or-file]"
    IO.println "Phases: parse, infer, eval, translate, scheme"
    IO.println ""
    IO.println "Examples:"
    IO.println "  ziku-test infer 'let x = 1 in x + 1'"
    IO.println "  ziku-test eval tests/golden/ir-eval/success/arithmetic.ziku"
    IO.println "  echo 'let x = 1 in x' | ziku-test infer"

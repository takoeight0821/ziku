import Ziku.Parser
import Ziku.Translate
import Ziku.IR.Eval

open Ziku
open Ziku.Translate
open Ziku.IR

-- Trace each step of evaluation
partial def traceEval (fuel : Nat) (s : Statement) : IO Unit := do
  IO.println s!"Step: {s}"
  if fuel == 0 then
    IO.println "Out of fuel"
    return
  match step s with
  | some s' =>
    IO.println "  → reduced"
    traceEval (fuel - 1) s'
  | none =>
    IO.println "  → stuck/terminal"
    match s with
    | .cut _ p (.covar _ "halt") =>
      if p.isValue then
        IO.println s!"  Terminal value: {p}"
      else
        IO.println s!"  Stuck (non-value): {p}"
    | _ =>
      IO.println s!"  Stuck (not terminal cut)"

-- Test substVar directly
def testSubstVar : IO Unit := do
  let dummyPos : SourcePos := { line := 0, col := 0 }
  -- Create: ifz(_ifz_cond, ⟨42 | halt⟩, ⟨0 | halt⟩)
  let s1 := Statement.cut dummyPos (Producer.lit dummyPos (.int 42)) (Consumer.covar dummyPos "halt")
  let s2 := Statement.cut dummyPos (Producer.lit dummyPos (.int 0)) (Consumer.covar dummyPos "halt")
  let ifzStmt := Statement.ifz dummyPos (Producer.var dummyPos "_ifz_cond") s1 s2
  IO.println s!"Before substVar: {ifzStmt}"
  -- Substitute _ifz_cond -> true
  let result := Statement.substVar "_ifz_cond" (Producer.lit dummyPos (.bool true)) ifzStmt
  IO.println s!"After substVar: {result}"

def main : IO UInt32 := do
  IO.println "=== Direct substVar test ==="
  testSubstVar
  IO.println ""

  let input := "let x = 10 in x + 1"
  IO.println s!"Input: {input}"
  IO.println ""

  match parseExprString input.trim with
  | .ok expr =>
    match translate expr with
    | .ok producer =>
      IO.println s!"IR: {producer}"
      IO.println ""
      let dummyPos : SourcePos := { line := 0, col := 0 }
      let stmt := Statement.cut dummyPos producer (Consumer.covar dummyPos "halt")
      IO.println "=== Evaluation trace ==="
      traceEval 20 stmt
    | .error e =>
      IO.println s!"Translation error: {e}"
  | .error e =>
    IO.println s!"Parse error: {e}"

  return 0

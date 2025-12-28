import Ziku.Parser
import Ziku.Translate
import Ziku.IR.Eval

open Ziku
open Ziku.Translate
open Ziku.IR

def testEval (input : String) : IO Unit := do
  match parseExprString input.trim with
  | .ok expr =>
    match translate expr with
    | .ok producer =>
      -- Connect to halt continuation
      let stmt := Statement.cut { line := 0, col := 0 } producer (Consumer.covar { line := 0, col := 0 } "halt")
      let result := Ziku.IR.eval stmt
      IO.println s!"Input: {input}"
      IO.println s!"IR: {producer}"
      IO.println s!"Result: {result}"
      IO.println ""
    | .error e =>
      IO.println s!"Translation error: {e}"
  | .error e =>
    IO.println s!"Parse error: {e}"

def main : IO UInt32 := do
  IO.println "=== IR Evaluation Tests ==="
  IO.println ""

  -- Test literal
  testEval "42"

  -- Test variable (will be stuck since unbound)
  -- testEval "x"

  -- Test binary operation
  testEval "1 + 2"

  -- Test nested binary operation
  testEval "1 + 2 * 3"

  -- Test comparison
  testEval "5 > 3"

  -- Test if
  testEval "if true then 1 else 0"

  -- Test if with comparison
  testEval "if 5 > 3 then 42 else 0"

  -- Test let binding
  testEval "let x = 10 in x + 1"

  -- Test nested let
  testEval "let x = 5 in let y = 3 in x + y"

  -- Test label (should just return the value)
  testEval "label result { 42 }"

  -- Test label with goto
  testEval "label result { if true then goto(100, result) else 0 }"

  -- Test label with nested goto
  testEval "label outer { let x = 10 in goto(x + 5, outer) }"

  return 0

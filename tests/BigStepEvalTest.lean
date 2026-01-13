import Ziku.IR.BigStepEval
import Ziku.Syntax

open Ziku
open Ziku.IR.BigStepEval

def testValueConstruction : IO Unit := do
  let v1 := Value.lit (.int 42)
  IO.println s!"Value 1: {v1}"
  let v2 := Value.lit (.bool true)
  IO.println s!"Value 2: {v2}"

def testEnvConstruction : IO Unit := do
  let env := Env.empty
  let v1 := Value.lit (.int 1)
  let env1 := env.insertVal "x" v1
  match env1.lookup "x" with
  | some (.val v) => IO.println s!"Found x: {v}"
  | _ => IO.println "Failed to find x"

def main : IO Unit := do
  testValueConstruction
  testEnvConstruction

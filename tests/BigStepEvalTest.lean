import Ziku.IR.BigStepEval
import Ziku.Syntax
import Ziku.IR.Syntax

open Ziku
open Ziku.IR
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

def testEvalLiteral : IO Unit := do
  let env := Env.empty
  let lit := Producer.lit synthesizedPos (.int 123)
  match ← evalProducer lit env with
  | .ok (.lit (.int 123)) => IO.println "Literal eval success"
  | .ok v => IO.println s!"Literal eval wrong value: {v}"
  | .error e => IO.println s!"Literal eval failed: {e}"

def testEvalVar : IO Unit := do
  let env := Env.empty.insertVal "y" (.lit (.int 456))
  let var := Producer.var synthesizedPos "y"
  match ← evalProducer var env with
  | .ok (.lit (.int 456)) => IO.println "Var eval success"
  | .ok v => IO.println s!"Var eval wrong value: {v}"
  | .error e => IO.println s!"Var eval failed: {e}"

def testEvalUnboundVar : IO Unit := do
  let env := Env.empty
  let var := Producer.var synthesizedPos "z"
  match ← evalProducer var env with
  | .error (.unboundVariable _ "z") => IO.println "Unbound var error success"
  | .ok v => IO.println s!"Unbound var expected error, got value: {v}"
  | .error e => IO.println s!"Unbound var expected unboundVariable error, got: {e}"

def testEvalBinOp : IO Unit := do
  let env := Env.empty
  let p1 := Producer.lit synthesizedPos (.int 10)
  let p2 := Producer.lit synthesizedPos (.int 20)
  let halt := Consumer.covar synthesizedPos "halt"
  
  -- Test Add
  let stmtAdd := Statement.binOp synthesizedPos .add p1 p2 halt
  match ← evalStatement stmtAdd env with
  | .ok (.lit (.int 30)) => IO.println "BinOp Add success"
  | .ok v => IO.println s!"BinOp Add wrong value: {v}"
  | .error e => IO.println s!"BinOp Add failed: {e}"

  -- Test Div by Zero
  let pZero := Producer.lit synthesizedPos (.int 0)
  let stmtDivZero := Statement.binOp synthesizedPos .div p1 pZero halt
  match ← evalStatement stmtDivZero env with
  | .error (.divisionByZero _) => IO.println "BinOp DivByZero success"
  | .ok v => IO.println s!"BinOp DivByZero expected error, got value: {v}"
  | .error e => IO.println s!"BinOp DivByZero expected divisionByZero, got: {e}"

  -- Test Type Mismatch
  let pBool := Producer.lit synthesizedPos (.bool true)
  let stmtMismatch := Statement.binOp synthesizedPos .add p1 pBool halt
  match ← evalStatement stmtMismatch env with
  | .error (.binOpTypeMismatch _ _ _ _) => IO.println "BinOp TypeMismatch success"
  | .ok v => IO.println s!"BinOp TypeMismatch expected error, got value: {v}"
  | .error e => IO.println s!"BinOp TypeMismatch expected binOpTypeMismatch, got: {e}"

def main : IO Unit := do
  testValueConstruction
  testEnvConstruction
  testEvalLiteral
  testEvalVar
  testEvalUnboundVar
  testEvalBinOp

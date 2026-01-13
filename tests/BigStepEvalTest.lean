import Ziku.IR.BigStepEval
import Ziku.Syntax
import Ziku.IR.Syntax

open Ziku
open Ziku.IR
open Ziku.IR.BigStepEval

namespace BigStepEvalTest

/-!
# Big-Step Evaluator Unit Tests

These are temporary unit tests to verify the incremental implementation of the big-step evaluator.
Once the implementation is complete and integrated, these should be replaced by or merged into
the golden test suite.
-/ 

def assert (msg : String) (cond : Bool) : IO Bool := do
  if !cond then
    IO.eprintln s!"[FAIL] {msg}"
    return false
  else
    IO.println s!"[PASS] {msg}"
    return true

def testValueConstruction : IO Bool := do
  let v1 := Value.lit (.int 42)
  let r1 ← assert "Value 1 is int 42" (match v1 with | .lit (.int 42) => true | _ => false)
  
  let v2 := Value.lit (.bool true)
  let r2 ← assert "Value 2 is bool true" (match v2 with | .lit (.bool true) => true | _ => false)
  return r1 && r2

def testEnvConstruction : IO Bool := do
  let env := Env.empty
  let v1 := Value.lit (.int 1)
  let env1 := env.insertVal "x" v1
  match env1.lookup "x" with
  | some (.val (.lit (.int 1))) => assert "Found x with value 1" true
  | _ => assert "Found x with value 1" false

def testEvalLiteral : IO Bool := do
  let env := Env.empty
  let lit := Producer.lit synthesizedPos (.int 123)
  match ← evalProducer lit env with
  | .ok (.lit (.int 123)) => assert "Literal eval success" true
  | .ok v => assert s!"Literal eval wrong value: {v}" false
  | .error e => assert s!"Literal eval failed: {e}" false

def testEvalVar : IO Bool := do
  let env := Env.empty.insertVal "y" (.lit (.int 456))
  let var := Producer.var synthesizedPos "y"
  match ← evalProducer var env with
  | .ok (.lit (.int 456)) => assert "Var eval success" true
  | .ok v => assert s!"Var eval wrong value: {v}" false
  | .error e => assert s!"Var eval failed: {e}" false

def testEvalUnboundVar : IO Bool := do
  let env := Env.empty
  let var := Producer.var synthesizedPos "z"
  match ← evalProducer var env with
  | .error (.unboundVariable _ "z") => assert "Unbound var error success" true
  | .ok v => assert s!"Unbound var expected error, got value: {v}" false
  | .error e => assert s!"Unbound var expected unboundVariable error, got: {e}" false

def testEvalBinOp : IO Bool := do
  let env := Env.empty
  let p1 := Producer.lit synthesizedPos (.int 10)
  let p2 := Producer.lit synthesizedPos (.int 20)
  let halt := Consumer.covar synthesizedPos "halt"
  
  -- Test Add
  let stmtAdd := Statement.binOp synthesizedPos .add p1 p2 halt
  let r1 ← match ← evalStatement stmtAdd env with
  | .ok (.lit (.int 30)) => assert "BinOp Add success" true
  | .ok v => assert s!"BinOp Add wrong value: {v}" false
  | .error e => assert s!"BinOp Add failed: {e}" false

  -- Test Div by Zero
  let pZero := Producer.lit synthesizedPos (.int 0)
  let stmtDivZero := Statement.binOp synthesizedPos .div p1 pZero halt
  let r2 ← match ← evalStatement stmtDivZero env with
  | .error (.divisionByZero _) => assert "BinOp DivByZero success" true
  | .ok v => assert s!"BinOp DivByZero expected error, got value: {v}" false
  | .error e => assert s!"BinOp DivByZero expected divisionByZero, got: {e}" false

  -- Test Type Mismatch
  let pBool := Producer.lit synthesizedPos (.bool true)
  let stmtMismatch := Statement.binOp synthesizedPos .add p1 pBool halt
  let r3 ← match ← evalStatement stmtMismatch env with
  | .error (.binOpTypeMismatch _ _ _ _) => assert "BinOp TypeMismatch success" true
  | .ok v => assert s!"BinOp TypeMismatch expected error, got value: {v}" false
  | .error e => assert s!"BinOp TypeMismatch expected binOpTypeMismatch, got: {e}" false

  return r1 && r2 && r3

def runTests : IO (Nat × Nat) := do
  IO.println "\n=== Big-Step Unit Tests ==="
  let tests := [
    testValueConstruction,
    testEnvConstruction,
    testEvalLiteral,
    testEvalVar,
    testEvalUnboundVar,
    testEvalBinOp
  ]
  let mut passed := 0
  let mut failed := 0
  for t in tests do
    if ← t then
      passed := passed + 1
    else
      failed := failed + 1
  return (passed, failed)

end BigStepEvalTest
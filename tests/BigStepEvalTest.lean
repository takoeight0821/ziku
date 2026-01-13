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
  | .jump _ _ => assert "Literal eval returned jump" false

def testEvalVar : IO Bool := do
  let env := Env.empty.insertVal "y" (.lit (.int 456))
  let var := Producer.var synthesizedPos "y"
  match ← evalProducer var env with
  | .ok (.lit (.int 456)) => assert "Var eval success" true
  | .ok v => assert s!"Var eval wrong value: {v}" false
  | .error e => assert s!"Var eval failed: {e}" false
  | .jump _ _ => assert "Var eval returned jump" false

def testEvalUnboundVar : IO Bool := do
  let env := Env.empty
  let var := Producer.var synthesizedPos "z"
  match ← evalProducer var env with
  | .error (.unboundVariable _ "z") => assert "Unbound var error success" true
  | .ok v => assert s!"Unbound var expected error, got value: {v}" false
  | .error e => assert s!"Unbound var expected unboundVariable error, got: {e}" false
  | .jump _ _ => assert "Unbound var returned jump" false

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
  | .jump _ _ => assert "BinOp Add returned jump" false

  -- Test Div by Zero
  let pZero := Producer.lit synthesizedPos (.int 0)
  let stmtDivZero := Statement.binOp synthesizedPos .div p1 pZero halt
  let r2 ← match ← evalStatement stmtDivZero env with
  | .error (.divisionByZero _) => assert "BinOp DivByZero success" true
  | .ok v => assert s!"BinOp DivByZero expected error, got value: {v}" false
  | .error e => assert s!"BinOp DivByZero expected divisionByZero, got: {e}" false
  | .jump _ _ => assert "BinOp DivByZero returned jump" false

  -- Test Type Mismatch
  let pBool := Producer.lit synthesizedPos (.bool true)
  let stmtMismatch := Statement.binOp synthesizedPos .add p1 pBool halt
  let r3 ← match ← evalStatement stmtMismatch env with
  | .error (.binOpTypeMismatch _ _ _ _) => assert "BinOp TypeMismatch success" true
  | .ok v => assert s!"BinOp TypeMismatch expected error, got value: {v}" false
  | .error e => assert s!"BinOp TypeMismatch expected binOpTypeMismatch, got: {e}" false
  | .jump _ _ => assert "BinOp TypeMismatch returned jump" false

  return r1 && r2 && r3

def testEvalLambda : IO Bool := do
  let env := Env.empty
  let pos := synthesizedPos
  -- \x. x  => cocase { ap(x, α) => <x | α> }
  let x := "x"
  let alpha := "alpha"
  let body := Statement.cut pos (.var pos x) (.covar pos alpha)
  let lambda := Producer.cocase pos [("ap", [x, alpha], body)]
  
  let arg := Producer.lit pos (.int 42)
  let halt := Consumer.covar pos "halt"
  
  -- Application: <lambda | ap(42; halt)>
  let stmtApp := Statement.cut pos lambda (.destructor pos "ap" [arg] halt)
  
  match ← evalStatement stmtApp env with
  | .ok (.lit (.int 42)) => assert "Lambda application success" true
  | .ok v => assert s!"Lambda application wrong value: {v}" false
  | .error e => assert s!"Lambda application failed: {e}" false
  | .jump _ _ => assert "Lambda application returned jump" false

def testEvalLabelGoto : IO Bool := do
  let env := Env.empty
  let pos := synthesizedPos
  let L := "L"
  let beta := "beta"
  let alpha := "alpha"
  let underscore := "_"
  
  -- label L { let _ = goto(42; L) in 99 }
  -- goto(42; L) => mu beta. <42 | L>
  let gotoStmt := Statement.cut pos (.lit pos (.int 42)) (.covar pos L)
  let gotoProd := Producer.mu pos beta gotoStmt
  
  -- let ... in 99 => mu alpha. < gotoProd | mu~_. <99 | alpha> >
  let letBody := Statement.cut pos (.lit pos (.int 99)) (.covar pos alpha)
  let letConsumer := Consumer.muTilde pos underscore letBody
  let letProd := Producer.mu pos alpha (Statement.cut pos gotoProd letConsumer)
  
  -- label L { letProd } => mu L. <letProd | L>
  let labelStmt := Statement.cut pos letProd (.covar pos L)
  let labelProd := Producer.mu pos L labelStmt
  
  -- Eval the whole thing (using explicit halt for top level)
  -- The mu L logic in Eval uses halt for the bound variable.
  -- But here we are manually calling evalProducer on labelProd.
  -- evalProducer (mu L...) will eval labelStmt with L=halt.
  
  match ← evalProducer labelProd env with
  | .ok (.lit (.int 42)) => assert "Label/Goto success (short-circuit)" true
  | .ok (.lit (.int 99)) => assert "Label/Goto failed: executed continuation (99) instead of jump" false
  | .ok v => assert s!"Label/Goto wrong value: {v}" false
  | .error e => assert s!"Label/Goto failed with error: {e}" false
  | .jump _ _ => assert "Label/Goto returned uncaught jump" false

def testEvalBuiltin : IO Bool := do
  let env := Env.empty
  let pos := synthesizedPos
  
  -- strLen("hello")
  let s := "hello"
  let arg := Producer.lit pos (.string s)
  let halt := Consumer.covar pos "halt"
  let builtinStmt := Statement.builtin pos .strLen [arg] halt
  
  match ← evalStatement builtinStmt env with
  | .ok (.lit (.int 5)) => assert "Builtin strLen success" true
  | .ok v => assert s!"Builtin strLen wrong value: {v}" false
  | .error e => assert s!"Builtin strLen failed: {e}" false
  | .jump _ _ => assert "Builtin strLen returned jump" false

def testEvalRecord : IO Bool := do
  let env := Env.empty
  let pos := synthesizedPos
  
  -- { x = 10, y = 20 }
  let fields := [
    ("x", Producer.lit pos (.int 10)),
    ("y", Producer.lit pos (.int 20))
  ]
  let record := Producer.record pos fields
  
  -- Access field x: <record | x(; halt)>
  let halt := Consumer.covar pos "halt"
  let stmtAccess := Statement.cut pos record (Consumer.destructor pos "x" [] halt)
  
  match ← evalStatement stmtAccess env with
  | .ok (.lit (.int 10)) => assert "Record field access success" true
  | .ok v => assert s!"Record field access wrong value: {v}" false
  | .error e => assert s!"Record field access failed: {e}" false
  | .jump _ _ => assert "Record field access returned jump" false

def runTests : IO (Nat × Nat) := do
  IO.println "\n=== Big-Step Unit Tests ==="
  let tests := [
    testValueConstruction,
    testEnvConstruction,
    testEvalLiteral,
    testEvalVar,
    testEvalUnboundVar,
    testEvalBinOp,
    testEvalLambda,
    testEvalLabelGoto,
    testEvalBuiltin,
    testEvalRecord
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
import Ziku.Syntax
import Ziku.IR.Syntax
import Ziku.IR.Eval

open Ziku Ziku.IR

def main : IO Unit := do
  let pos : SourcePos := { line := 0, col := 0 }
  let env := Env.empty
  
  -- Test variable binding
  let p := Producer.lit pos (.int 42)
  let env' := env.extend "x" (.closure p env)
  
  match env'.lookup "x" with
  | some (.closure p' _) => 
    if p' == p then
      IO.println "Variable lookup success"
    else
      IO.println "Variable lookup mismatch"
  | _ => IO.println "Variable lookup failed"

  -- Test covariable binding
  let c := Consumer.covar pos "alpha"
  let env'' := env'.extend "beta" (.covarClosure c env')
  
  match env''.lookup "beta" with
  | some (.covarClosure c' _) =>
    if c' == c then
      IO.println "Covariable lookup success"
    else
      IO.println "Covariable lookup mismatch"
  | _ => IO.println "Covariable lookup failed"

namespace Ziku

inductive Expr where
  | lit  : Int → Expr
  | var  : String → Expr
  | add  : Expr → Expr → Expr
  | sub  : Expr → Expr → Expr
  | mul  : Expr → Expr → Expr
  | div  : Expr → Expr → Expr
  deriving Repr, BEq, DecidableEq

-- Expression size (for induction)
def Expr.size : Expr → Nat
  | lit _ => 1
  | var _ => 1
  | add e1 e2 => 1 + e1.size + e2.size
  | sub e1 e2 => 1 + e1.size + e2.size
  | mul e1 e2 => 1 + e1.size + e2.size
  | div e1 e2 => 1 + e1.size + e2.size

-- Free variables in an expression
def Expr.freeVars : Expr → List String
  | lit _ => []
  | var x => [x]
  | add e1 e2 => e1.freeVars ++ e2.freeVars
  | sub e1 e2 => e1.freeVars ++ e2.freeVars
  | mul e1 e2 => e1.freeVars ++ e2.freeVars
  | div e1 e2 => e1.freeVars ++ e2.freeVars

-- Closed expression (no free variables)
def Expr.closed (e : Expr) : Prop := e.freeVars = []

end Ziku

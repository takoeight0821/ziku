namespace Ziku

inductive Expr where
  | lit  : Int → Expr
  | var  : String → Expr
  | add  : Expr → Expr → Expr
  | sub  : Expr → Expr → Expr
  | mul  : Expr → Expr → Expr
  | div  : Expr → Expr → Expr
  deriving Repr, BEq

end Ziku

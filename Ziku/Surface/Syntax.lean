import Ziku.Syntax

namespace Ziku.Surface

/-!
# Surface Language AST

The surface language is the user-facing language with intuitive control flow
constructs (`label` and `goto`) instead of the lower-level sequent calculus
primitives.
-/

open Ziku (SourcePos Ident BinOp UnaryOp Lit Ty Pat Accessor Copattern)

-- Surface expressions
inductive Expr where
  | lit       : SourcePos → Lit → Expr                              -- Literal: 42
  | var       : SourcePos → Ident → Expr                            -- Variable: x
  | binOp     : SourcePos → BinOp → Expr → Expr → Expr              -- Binary op: a + b
  | unaryOp   : SourcePos → UnaryOp → Expr → Expr                   -- Unary op: -x, not p
  | lam       : SourcePos → Ident → Bool → Expr → Expr              -- Lambda: \x => e or \~k => e
  | app       : SourcePos → Expr → Expr → Bool → Expr               -- Application: f x or f (~k)
  | let_      : SourcePos → Ident → Option Ty → Expr → Expr → Expr  -- Let: let x : ty = e in body
  | letRec    : SourcePos → Ident → Option Ty → Expr → Expr → Expr  -- Let rec: let rec f = e in body
  | match_    : SourcePos → Expr → List (Pat × Expr) → Expr         -- Match: match e with | p => e end
  | codata    : SourcePos → List (List Pat × Copattern × Expr) → Expr  -- Codata block: { patterns # copat => e, ... }
  | field     : SourcePos → Expr → Ident → Expr                     -- Field access: e.field
  | ann       : SourcePos → Expr → Ty → Expr                        -- Type annotation: (e : ty)
  | record    : SourcePos → List (Ident × Expr) → Expr              -- Anonymous record: { x = 1, y = 2 }
  | if_       : SourcePos → Expr → Expr → Expr → Expr               -- If: if c then t else f
  | hash      : SourcePos → Expr                                    -- Self-reference: # (for codata)
  | label     : SourcePos → Ident → Expr → Expr                     -- Label: label name { body }
  | goto      : SourcePos → Expr → Expr → Expr                      -- Goto: goto(expr, covalue_expr)
  | con       : SourcePos → Ident → List Expr → Expr                -- Constructor: Con args...
  deriving Repr, BEq

-- Get source position from Expr
def Expr.pos : Expr → SourcePos
  | lit p _ => p
  | var p _ => p
  | binOp p _ _ _ => p
  | unaryOp p _ _ => p
  | lam p _ _ _ => p
  | app p _ _ _ => p
  | let_ p _ _ _ _ => p
  | letRec p _ _ _ _ => p
  | match_ p _ _ => p
  | codata p _ => p
  | field p _ _ => p
  | ann p _ _ => p
  | record p _ => p
  | if_ p _ _ _ => p
  | hash p => p
  | label p _ _ => p
  | goto p _ _ => p
  | con p _ _ => p

-- Expression size
partial def Expr.exprSize : Expr → Nat
  | lit _ _ => 1
  | var _ _ => 1
  | binOp _ _ e1 e2 => 1 + e1.exprSize + e2.exprSize
  | unaryOp _ _ e => 1 + e.exprSize
  | lam _ _ _ e => 1 + e.exprSize
  | app _ e1 e2 _ => 1 + e1.exprSize + e2.exprSize
  | let_ _ _ _ e1 e2 => 1 + e1.exprSize + e2.exprSize
  | letRec _ _ _ e1 e2 => 1 + e1.exprSize + e2.exprSize
  | match_ _ e _ => 1 + e.exprSize
  | codata _ _ => 1
  | field _ e _ => 1 + e.exprSize
  | ann _ e _ => 1 + e.exprSize
  | record _ _ => 1
  | if_ _ c t f => 1 + c.exprSize + t.exprSize + f.exprSize
  | hash _ => 1
  | label _ _ e => 1 + e.exprSize
  | goto _ e1 e2 => 1 + e1.exprSize + e2.exprSize
  | con _ _ args => 1 + args.foldl (fun acc e => acc + e.exprSize) 0

-- Free variables in an expression
partial def Expr.freeVars : Expr → List Ident
  | lit _ _ => []
  | var _ x => [x]
  | binOp _ _ e1 e2 => e1.freeVars ++ e2.freeVars
  | unaryOp _ _ e => e.freeVars
  | lam _ x _ e => e.freeVars.filter (fun v => v != x)
  | app _ e1 e2 _ => e1.freeVars ++ e2.freeVars
  | let_ _ x _ e1 e2 => e1.freeVars ++ e2.freeVars.filter (· != x)
  | letRec _ x _ e1 e2 =>
    e1.freeVars.filter (· != x) ++ e2.freeVars.filter (· != x)
  | match_ _ e cases =>
    e.freeVars ++ (cases.map (fun (_, body) => body.freeVars)).flatten
  | codata _ clauses =>
    (clauses.map (fun (_, _, body) => body.freeVars)).flatten
  | field _ e _ => e.freeVars
  | ann _ e _ => e.freeVars
  | record _ fields => (fields.map (fun (_, e) => e.freeVars)).flatten
  | if_ _ c t f => c.freeVars ++ t.freeVars ++ f.freeVars
  | hash _ => []
  | label _ name e => e.freeVars.filter (· != name)  -- name is bound as a label
  | goto _ e1 e2 => e1.freeVars ++ e2.freeVars
  | con _ _ args => args.flatMap Expr.freeVars

-- Closed expression (no free variables)
def Expr.closed (e : Expr) : Prop := e.freeVars = []

-- Pretty print expressions
partial def Expr.toString : Expr → String
  | .lit _ l => s!"(Lit {l})"
  | .var _ x => s!"(Var \"{x}\")"
  | .binOp _ op e1 e2 => s!"(BinOp {op} {e1.toString} {e2.toString})"
  | .unaryOp _ op e => s!"(UnaryOp {op} {e.toString})"
  | .lam _ p isCov body => 
    let pStr := if isCov then s!"~{p}" else p
    s!"(Lam \"{pStr}\" {body.toString})"
  | .app _ e1 e2 isCov => 
    let e2Str := if isCov then s!"~{e2.toString}" else e2.toString
    s!"(App {e1.toString} {e2Str})"
  | .let_ _ x ty e1 e2 =>
    let tyStr := match ty with | some t => s!" : {t}" | none => ""
    s!"(Let \"{x}\"{tyStr} {e1.toString} {e2.toString})"
  | .letRec _ x ty e1 e2 =>
    let tyStr := match ty with | some t => s!" : {t}" | none => ""
    s!"(LetRec \"{x}\"{tyStr} {e1.toString} {e2.toString})"
  | .match_ _ e cases =>
    let cs := cases.map (fun (p, body) => s!"({p} => {body.toString})")
    s!"(Match {e.toString} [{String.intercalate ", " cs}])"
  | .codata _ clauses =>
    let cs := clauses.map (fun (ps, cp, body) =>
      let psStr := if ps.isEmpty then "" else String.intercalate " " (ps.map Ziku.Pat.toString) ++ " "
      s!"({psStr}#{Ziku.Copattern.toString cp} => {body.toString})")
    s!"(Codata [{String.intercalate ", " cs}])"
  | .field _ e f => s!"(Field {e.toString} \"{f}\")"
  | .ann _ e ty => s!"(Ann {e.toString} {ty})"
  | .record _ fields =>
    let fs := fields.map (fun (n, e) => s!"{n} = {e.toString}")
    "(Record { " ++ String.intercalate ", " fs ++ " })"
  | .if_ _ c t f => s!"(If {c.toString} {t.toString} {f.toString})"
  | .hash _ => "#"
  | .label _ name body => s!"(Label \"{name}\" {body.toString})"
  | .goto _ e1 e2 => s!"(Goto {e1.toString} {e2.toString})"
  | .con _ name args =>
    let argsStr := args.map Expr.toString
    s!"(Con \"{name}\" [{String.intercalate ", " argsStr}])"

instance : ToString Expr := ⟨Expr.toString⟩

end Ziku.Surface

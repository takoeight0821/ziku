namespace Ziku

/-!
# Ziku Abstract Syntax Tree

This module defines the complete AST for the Ziku programming language,
a duality-aware language with explicit data/codata symmetry and
copattern matching support.
-/

-- Source location for error messages
structure SourcePos where
  line : Nat := 1
  col : Nat := 1
  deriving Repr, BEq, Inhabited

structure Span where
  start : SourcePos
  stop : SourcePos
  deriving Repr, BEq, Inhabited

-- Names and identifiers
abbrev Ident := String

-- Binary operators
inductive BinOp where
  -- Arithmetic
  | add | sub | mul | div
  -- Comparison
  | eq | ne | lt | le | gt | ge
  -- Logical
  | and | or
  -- Other
  | concat  -- ++
  | pipe    -- |>
  deriving Repr, BEq, DecidableEq

-- Unary operators
inductive UnaryOp where
  | neg   -- -
  | not   -- not
  deriving Repr, BEq, DecidableEq

-- Literals
inductive Lit where
  | int    : Int → Lit
  | float  : Float → Lit
  | string : String → Lit
  | char   : Char → Lit
  | bool   : Bool → Lit
  | unit   : Lit
  deriving Repr, BEq

-- Types
inductive Ty where
  | var     : SourcePos → Ident → Ty                              -- Type variable: a
  | con     : SourcePos → Ident → Ty                              -- Type constructor: Int, Bool
  | app     : SourcePos → Ty → Ty → Ty                            -- Type application: List a
  | arrow   : SourcePos → Ty → Ty → Ty                            -- Function type: a -> b
  | forall_ : SourcePos → Ident → Ty → Ty                         -- Polymorphic: forall a. a -> a
  | record  : SourcePos → List (Ident × Ty) → Option Ty → Ty      -- Record type: { x : Int | ρ }
  | variant : SourcePos → List (Ident × List Ty) → Option Ty → Ty -- Variant type: [Cons Int a | Nil | ρ]
  | bottom  : SourcePos → Ty                                      -- Bottom type: ⊥ (never returns)
  deriving Repr, BEq

-- Get source position from Ty
def Ty.pos : Ty → SourcePos
  | var p _ => p
  | con p _ => p
  | app p _ _ => p
  | arrow p _ _ => p
  | forall_ p _ _ => p
  | record p _ _ => p
  | variant p _ _ => p
  | bottom p => p

-- Check if type is bottom
def Ty.isBottom : Ty → Bool
  | bottom _ => true
  | _ => false

-- Patterns (for data destructuring)
inductive Pat where
  | var     : SourcePos → Ident → Pat                     -- Variable pattern: x
  | lit     : SourcePos → Lit → Pat                       -- Literal pattern: 42, "hello"
  | wild    : SourcePos → Pat                             -- Wildcard: _
  | con     : SourcePos → Ident → List Pat → Pat          -- Constructor: Cons x xs
  | paren   : SourcePos → Pat → Pat                       -- Parenthesized: (p)
  | ann     : SourcePos → Pat → Ty → Pat                  -- Annotated: (p : ty)
  deriving Repr, BEq

-- Get source position from Pat
def Pat.pos : Pat → SourcePos
  | var p _ => p
  | lit p _ => p
  | wild p => p
  | con p _ _ => p
  | paren p _ => p
  | ann p _ _ => p

-- Copattern accessor (for codata construction)
inductive Accessor where
  | field : Ident → Accessor                  -- .field
  | apply : Ident → Accessor                  -- (arg)
  deriving Repr, BEq

-- Copattern (sequence of accessors)
-- e.g., #.tail.head becomes [.tail, .head]
-- e.g., #(x) becomes [(x)]
abbrev Copattern := List Accessor

-- Expressions
inductive Expr where
  | lit       : SourcePos → Lit → Expr                              -- Literal: 42
  | var       : SourcePos → Ident → Expr                            -- Variable: x
  | binOp     : SourcePos → BinOp → Expr → Expr → Expr              -- Binary op: a + b
  | unaryOp   : SourcePos → UnaryOp → Expr → Expr                   -- Unary op: -x, not p
  | lam       : SourcePos → Ident → Expr → Expr                     -- Lambda: \x => e
  | app       : SourcePos → Expr → Expr → Expr                      -- Application: f x
  | let_      : SourcePos → Ident → Option Ty → Expr → Expr → Expr  -- Let: let x : ty = e in body
  | letRec    : SourcePos → Ident → Option Ty → Expr → Expr → Expr  -- Let rec: let rec f = e in body
  | match_    : SourcePos → Expr → List (Pat × Expr) → Expr         -- Match: match e with | p => e end
  | codata    : SourcePos → List (List Pat × Copattern × Expr) → Expr  -- Codata block: { patterns # copat => e, ... }
  | field     : SourcePos → Expr → Ident → Expr                     -- Field access: e.field
  | ann       : SourcePos → Expr → Ty → Expr                        -- Type annotation: (e : ty)
  | record    : SourcePos → List (Ident × Expr) → Expr              -- Anonymous record: { x = 1, y = 2 }
  | if_       : SourcePos → Expr → Expr → Expr → Expr               -- If: if c then t else f
  | cut       : SourcePos → Expr → Expr → Expr                      -- Sequent cut: cut <producer | consumer>
  | mu        : SourcePos → Ident → Expr → Expr                     -- μ-abstraction: μk => e
  | hash      : SourcePos → Expr                                    -- Self-reference: # (for codata)
  | label     : SourcePos → Ident → Expr → Expr                     -- Label: label name { body }
  | goto      : SourcePos → Expr → Ident → Expr                     -- Goto: goto(expr, name)
  | con       : SourcePos → Ident → List Expr → Expr                -- Constructor: Con args...
  deriving Repr, BEq

-- Get source position from Expr
def Expr.pos : Expr → SourcePos
  | lit p _ => p
  | var p _ => p
  | binOp p _ _ _ => p
  | unaryOp p _ _ => p
  | lam p _ _ => p
  | app p _ _ => p
  | let_ p _ _ _ _ => p
  | letRec p _ _ _ _ => p
  | match_ p _ _ => p
  | codata p _ => p
  | field p _ _ => p
  | ann p _ _ => p
  | record p _ => p
  | if_ p _ _ _ => p
  | cut p _ _ => p
  | mu p _ _ => p
  | hash p => p
  | label p _ _ => p
  | goto p _ _ => p
  | con p _ _ => p

-- Data constructor declaration
structure ConDecl where
  name : Ident
  args : List Ty
  deriving Repr, BEq

-- Codata signature (copattern signature)
structure CopatSig where
  accessors : Copattern
  ty : Ty
  deriving Repr, BEq

-- Clause for function definition
inductive DefClause where
  | patClause   : List Pat → Expr → DefClause                    -- | p1, p2 => e
  | copatClause : List Pat → Copattern → Expr → DefClause        -- p1, p2 #.field => e
  deriving Repr, BEq

-- Top-level declarations
inductive Decl where
  | data    : Ident → List Ident → List ConDecl → Decl          -- data T a = | C1 | C2
  | codata  : Ident → List Ident → List CopatSig → Decl         -- codata T a { #.f : ty }
  | def_    : Ident → Ty → Expr → Decl                          -- def f : ty = e
  | defPat  : Ident → Ty → List DefClause → Decl                -- def f : ty | p => e
  | infix_  : Nat → Bool → Ident → Decl                         -- infix 6 ++  (prec, rightAssoc, name)
  | module_ : Ident → List Decl → Decl                          -- module M where ... end
  | import_ : Ident → Option (List Ident) → Option Ident → Decl -- import M / import M (a, b) / import M as N
  deriving Repr, BEq

-- A program is a list of declarations
abbrev Program := List Decl

-- Helper functions

-- Expression size (manual implementation)
partial def Expr.exprSize : Expr → Nat
  | lit _ _ => 1
  | var _ _ => 1
  | binOp _ _ e1 e2 => 1 + e1.exprSize + e2.exprSize
  | unaryOp _ _ e => 1 + e.exprSize
  | lam _ _ e => 1 + e.exprSize
  | app _ e1 e2 => 1 + e1.exprSize + e2.exprSize
  | let_ _ _ _ e1 e2 => 1 + e1.exprSize + e2.exprSize
  | letRec _ _ _ e1 e2 => 1 + e1.exprSize + e2.exprSize
  | match_ _ e _ => 1 + e.exprSize
  | codata _ _ => 1
  | field _ e _ => 1 + e.exprSize
  | ann _ e _ => 1 + e.exprSize
  | record _ _ => 1
  | if_ _ c t f => 1 + c.exprSize + t.exprSize + f.exprSize
  | cut _ e1 e2 => 1 + e1.exprSize + e2.exprSize
  | mu _ _ e => 1 + e.exprSize
  | hash _ => 1
  | label _ _ e => 1 + e.exprSize
  | goto _ e _ => 1 + e.exprSize
  | con _ _ args => 1 + args.foldl (fun acc e => acc + e.exprSize) 0

-- Free variables in an expression
partial def Expr.freeVars : Expr → List Ident
  | lit _ _ => []
  | var _ x => [x]
  | binOp _ _ e1 e2 => e1.freeVars ++ e2.freeVars
  | unaryOp _ _ e => e.freeVars
  | lam _ x e => e.freeVars.filter (fun v => v != x)
  | app _ e1 e2 => e1.freeVars ++ e2.freeVars
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
  | cut _ e1 e2 => e1.freeVars ++ e2.freeVars
  | mu _ x e => e.freeVars.filter (· != x)
  | hash _ => []
  | label _ name e => e.freeVars.filter (· != name)  -- name is bound as a label
  | goto _ e _ => e.freeVars
  | con _ _ args => args.flatMap Expr.freeVars

-- Closed expression (no free variables)
def Expr.closed (e : Expr) : Prop := e.freeVars = []

-- Pretty printing helpers
def BinOp.toString : BinOp → String
  | .add => "+"
  | .sub => "-"
  | .mul => "*"
  | .div => "/"
  | .eq => "=="
  | .ne => "!="
  | .lt => "<"
  | .le => "<="
  | .gt => ">"
  | .ge => ">="
  | .and => "&&"
  | .or => "||"
  | .concat => "++"
  | .pipe => "|>"

instance : ToString BinOp := ⟨BinOp.toString⟩

def UnaryOp.toString : UnaryOp → String
  | .neg => "-"
  | .not => "not"

instance : ToString UnaryOp := ⟨UnaryOp.toString⟩

def Lit.toString : Lit → String
  | .int n => s!"{n}"
  | .float f => s!"{f}"
  | .string s => s!"\"{s}\""
  | .char c => s!"'{c}'"
  | .bool b => if b then "true" else "false"
  | .unit => "()"

instance : ToString Lit := ⟨Lit.toString⟩

-- Pretty print types
partial def Ty.toString : Ty → String
  | .var _ x => x
  | .con _ c => c
  | .app _ t1 t2 => s!"({t1.toString} {t2.toString})"
  | .arrow _ t1 t2 => s!"({t1.toString} -> {t2.toString})"
  | .forall_ _ x t => s!"(forall {x}. {t.toString})"
  | .record _ fields rowTail =>
    let fs := fields.map (fun (n, t) => s!"{n} : {t.toString}")
    match rowTail with
    | none => "{ " ++ String.intercalate ", " fs ++ " }"
    | some r => "{ " ++ String.intercalate ", " fs ++ " | " ++ r.toString ++ " }"
  | .variant _ cases rowTail =>
    let cs := cases.map (fun (c, tys) =>
      if tys.isEmpty then c
      else s!"{c}(" ++ String.intercalate ", " (tys.map Ty.toString) ++ ")")
    match rowTail with
    | none => "[" ++ String.intercalate " | " cs ++ "]"
    | some r => "[" ++ String.intercalate " | " cs ++ " | " ++ r.toString ++ "]"
  | .bottom _ => "⊥"

instance : ToString Ty := ⟨Ty.toString⟩

-- Pretty print patterns
partial def Pat.toString : Pat → String
  | .var _ x => x
  | .lit _ l => l.toString
  | .wild _ => "_"
  | .con _ c [] => c
  | .con _ c ps => s!"({c} {String.intercalate " " (ps.map Pat.toString)})"
  | .paren _ p => s!"({p.toString})"
  | .ann _ p ty => s!"({p.toString} : {ty})"

instance : ToString Pat := ⟨Pat.toString⟩

-- Pretty print accessors
def Accessor.toString : Accessor → String
  | .field f => s!".{f}"
  | .apply x => s!"({x})"

instance : ToString Accessor := ⟨Accessor.toString⟩

-- Pretty print copattern
def Copattern.toString (cp : Copattern) : String :=
  String.join (cp.map Accessor.toString)

-- Pretty print expressions
partial def Expr.toString : Expr → String
  | .lit _ l => s!"(Lit {l})"
  | .var _ x => s!"(Var \"{x}\")"
  | .binOp _ op e1 e2 => s!"(BinOp {op} {e1.toString} {e2.toString})"
  | .unaryOp _ op e => s!"(UnaryOp {op} {e.toString})"
  | .lam _ p body => s!"(Lam \"{p}\" {body.toString})"
  | .app _ e1 e2 => s!"(App {e1.toString} {e2.toString})"
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
      let psStr := if ps.isEmpty then "" else String.intercalate " " (ps.map Pat.toString) ++ " "
      s!"({psStr}#{Copattern.toString cp} => {body.toString})")
    s!"(Codata [{String.intercalate ", " cs}])"
  | .field _ e f => s!"(Field {e.toString} \"{f}\")"
  | .ann _ e ty => s!"(Ann {e.toString} {ty})"
  | .record _ fields =>
    let fs := fields.map (fun (n, e) => s!"{n} = {e.toString}")
    "(Record { " ++ String.intercalate ", " fs ++ " })"
  | .if_ _ c t f => s!"(If {c.toString} {t.toString} {f.toString})"
  | .cut _ e1 e2 => s!"(Cut {e1.toString} {e2.toString})"
  | .mu _ x e => s!"(Mu \"{x}\" {e.toString})"
  | .hash _ => "#"
  | .label _ name body => s!"(Label \"{name}\" {body.toString})"
  | .goto _ e name => s!"(Goto {e.toString} \"{name}\")"
  | .con _ name args =>
    let argsStr := args.map Expr.toString
    s!"(Con \"{name}\" [{String.intercalate ", " argsStr}])"

instance : ToString Expr := ⟨Expr.toString⟩

-- Pretty print declarations
partial def Decl.toString : Decl → String
  | .data name params constrs =>
    let ps := if params.isEmpty then "" else " " ++ String.intercalate " " params
    let cs := constrs.map (fun c =>
      let args := if c.args.isEmpty then "" else " " ++ String.intercalate " " (c.args.map Ty.toString)
      s!"| {c.name}{args}")
    s!"(Data {name}{ps} [{String.intercalate " " cs}])"
  | .codata name params sigs =>
    let ps := if params.isEmpty then "" else " " ++ String.intercalate " " params
    let ss := sigs.map (fun s => s!"#{Copattern.toString s.accessors} : {s.ty}")
    s!"(Codata {name}{ps} " ++ "{ " ++ String.intercalate ", " ss ++ " })"
  | .def_ name ty body =>
    s!"(Def \"{name}\" {ty} {body.toString})"
  | .defPat name ty _clauses =>
    s!"(DefPat \"{name}\" {ty} [...])"
  | .infix_ prec rightAssoc op =>
    let assoc := if rightAssoc then "right" else "left"
    s!"(Infix {prec} {assoc} \"{op}\")"
  | .module_ name _decls =>
    s!"(Module {name} [...])"
  | .import_ name _items _alias =>
    s!"(Import {name})"

instance : ToString Decl := ⟨Decl.toString⟩

end Ziku

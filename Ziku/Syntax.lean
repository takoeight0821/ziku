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
  | var     : Ident → Ty                      -- Type variable: a
  | con     : Ident → Ty                      -- Type constructor: Int, Bool
  | app     : Ty → Ty → Ty                    -- Type application: List a
  | arrow   : Ty → Ty → Ty                    -- Function type: a -> b
  | forall_ : Ident → Ty → Ty                 -- Polymorphic: forall a. a -> a
  | record  : List (Ident × Ty) → Ty          -- Record type: { x : Int, y : Int }
  deriving Repr, BEq

-- Patterns (for data destructuring)
inductive Pat where
  | var     : Ident → Pat                     -- Variable pattern: x
  | lit     : Lit → Pat                       -- Literal pattern: 42, "hello"
  | wild    : Pat                             -- Wildcard: _
  | con     : Ident → List Pat → Pat          -- Constructor: Cons x xs
  | paren   : Pat → Pat                       -- Parenthesized: (p)
  | ann     : Pat → Ty → Pat                  -- Annotated: (p : ty)
  deriving Repr, BEq

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
  | lit       : Lit → Expr                              -- Literal: 42
  | var       : Ident → Expr                            -- Variable: x
  | hash      : Expr                                    -- The # symbol (self-reference)
  | binOp     : BinOp → Expr → Expr → Expr              -- Binary op: a + b
  | unaryOp   : UnaryOp → Expr → Expr                   -- Unary op: -x, not p
  | lam       : List Ident → Expr → Expr                -- Lambda: \x, y => e
  | app       : Expr → Expr → Expr                      -- Application: f x
  | let_      : Ident → Option Ty → Expr → Expr → Expr  -- Let: let x : ty = e in body
  | letRec    : Ident → Option Ty → Expr → Expr → Expr  -- Let rec: let rec f = e in body
  | match_    : Expr → List (Pat × Expr) → Expr         -- Match: match e with | p => e end
  | codata    : List (List Pat × Copattern × Expr) → Expr  -- Codata block: { patterns # copat => e, ... }
  | field     : Expr → Ident → Expr                     -- Field access: e.field
  | ann       : Expr → Ty → Expr                        -- Type annotation: (e : ty)
  | record    : List (Ident × Expr) → Expr              -- Anonymous record: { x = 1, y = 2 }
  | if_       : Expr → Expr → Expr → Expr               -- If: if c then t else f
  | cut       : Expr → Expr → Expr                      -- Sequent cut: cut <producer | consumer>
  | mu        : Ident → Expr → Expr                     -- μ-abstraction: μk => e
  deriving Repr, BEq

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
  | lit _ => 1
  | var _ => 1
  | hash => 1
  | binOp _ e1 e2 => 1 + e1.exprSize + e2.exprSize
  | unaryOp _ e => 1 + e.exprSize
  | lam _ e => 1 + e.exprSize
  | app e1 e2 => 1 + e1.exprSize + e2.exprSize
  | let_ _ _ e1 e2 => 1 + e1.exprSize + e2.exprSize
  | letRec _ _ e1 e2 => 1 + e1.exprSize + e2.exprSize
  | match_ e _ => 1 + e.exprSize
  | codata _ => 1
  | field e _ => 1 + e.exprSize
  | ann e _ => 1 + e.exprSize
  | record _ => 1
  | if_ c t f => 1 + c.exprSize + t.exprSize + f.exprSize
  | cut e1 e2 => 1 + e1.exprSize + e2.exprSize
  | mu _ e => 1 + e.exprSize

-- Free variables in an expression
partial def Expr.freeVars : Expr → List Ident
  | lit _ => []
  | var x => [x]
  | hash => []
  | binOp _ e1 e2 => e1.freeVars ++ e2.freeVars
  | unaryOp _ e => e.freeVars
  | lam xs e => e.freeVars.filter (fun v => !xs.contains v)
  | app e1 e2 => e1.freeVars ++ e2.freeVars
  | let_ x _ e1 e2 => e1.freeVars ++ e2.freeVars.filter (· != x)
  | letRec x _ e1 e2 =>
    e1.freeVars.filter (· != x) ++ e2.freeVars.filter (· != x)
  | match_ e cases =>
    e.freeVars ++ (cases.map (fun (_, body) => body.freeVars)).flatten
  | codata clauses =>
    (clauses.map (fun (_, _, body) => body.freeVars)).flatten
  | field e _ => e.freeVars
  | ann e _ => e.freeVars
  | record fields => (fields.map (fun (_, e) => e.freeVars)).flatten
  | if_ c t f => c.freeVars ++ t.freeVars ++ f.freeVars
  | cut e1 e2 => e1.freeVars ++ e2.freeVars
  | mu x e => e.freeVars.filter (· != x)

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
  | .var x => x
  | .con c => c
  | .app t1 t2 => s!"({t1.toString} {t2.toString})"
  | .arrow t1 t2 => s!"({t1.toString} -> {t2.toString})"
  | .forall_ x t => s!"(forall {x}. {t.toString})"
  | .record fields =>
    let fs := fields.map (fun (n, t) => s!"{n} : {t.toString}")
    "{ " ++ String.intercalate ", " fs ++ " }"

instance : ToString Ty := ⟨Ty.toString⟩

-- Pretty print patterns
partial def Pat.toString : Pat → String
  | .var x => x
  | .lit l => l.toString
  | .wild => "_"
  | .con c [] => c
  | .con c ps => s!"({c} {String.intercalate " " (ps.map Pat.toString)})"
  | .paren p => s!"({p.toString})"
  | .ann p ty => s!"({p.toString} : {ty})"

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
  | .lit l => s!"(Lit {l})"
  | .var x => s!"(Var \"{x}\")"
  | .hash => "#"
  | .binOp op e1 e2 => s!"(BinOp {op} {e1.toString} {e2.toString})"
  | .unaryOp op e => s!"(UnaryOp {op} {e.toString})"
  | .lam ps body => s!"(Lam [{String.intercalate ", " (ps.map (s!"\"{·}\""))}] {body.toString})"
  | .app e1 e2 => s!"(App {e1.toString} {e2.toString})"
  | .let_ x ty e1 e2 =>
    let tyStr := match ty with | some t => s!" : {t}" | none => ""
    s!"(Let \"{x}\"{tyStr} {e1.toString} {e2.toString})"
  | .letRec x ty e1 e2 =>
    let tyStr := match ty with | some t => s!" : {t}" | none => ""
    s!"(LetRec \"{x}\"{tyStr} {e1.toString} {e2.toString})"
  | .match_ e cases =>
    let cs := cases.map (fun (p, body) => s!"({p} => {body.toString})")
    s!"(Match {e.toString} [{String.intercalate ", " cs}])"
  | .codata clauses =>
    let cs := clauses.map (fun (ps, cp, body) =>
      let psStr := if ps.isEmpty then "" else String.intercalate " " (ps.map Pat.toString) ++ " "
      s!"({psStr}#{Copattern.toString cp} => {body.toString})")
    s!"(Codata [{String.intercalate ", " cs}])"
  | .field e f => s!"(Field {e.toString} \"{f}\")"
  | .ann e ty => s!"(Ann {e.toString} {ty})"
  | .record fields =>
    let fs := fields.map (fun (n, e) => s!"{n} = {e.toString}")
    "(Record { " ++ String.intercalate ", " fs ++ " })"
  | .if_ c t f => s!"(If {c.toString} {t.toString} {f.toString})"
  | .cut e1 e2 => s!"(Cut {e1.toString} {e2.toString})"
  | .mu x e => s!"(Mu \"{x}\" {e.toString})"

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
  | .defPat name ty clauses =>
    s!"(DefPat \"{name}\" {ty} [...])"
  | .infix_ prec rightAssoc op =>
    let assoc := if rightAssoc then "right" else "left"
    s!"(Infix {prec} {assoc} \"{op}\")"
  | .module_ name decls =>
    s!"(Module {name} [...])"
  | .import_ name items alias =>
    s!"(Import {name})"

instance : ToString Decl := ⟨Decl.toString⟩

end Ziku

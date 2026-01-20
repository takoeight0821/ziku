namespace Ziku

/-!
# Ziku Abstract Syntax Tree

This module defines the complete AST for the Ziku programming language,
a duality-aware language with explicit data/codata symmetry and
copattern matching support.
-/

-- Source location for error messages
/-- Represents a position in the source code (line and column). -/
structure SourcePos where
  /-- Line number (1-based). -/
  line : Nat := 1
  /-- Column number (1-based). -/
  col : Nat := 1
  deriving Repr, BEq, Inhabited

instance : ToString SourcePos where
  toString pos := s!"{pos.line}:{pos.col}"

-- Default position for synthesized/generated code
/-- A special position used for code that was not directly written by the user. -/
def synthesizedPos : SourcePos := { line := 0, col := 0 }

/-- Represents a range of source code (start and stop positions). -/
structure Span where
  /-- Starting position of the span. -/
  start : SourcePos
  /-- Ending position of the span. -/
  stop : SourcePos
  deriving Repr, BEq, Inhabited

-- Names and identifiers
/-- Type alias for identifiers (variable names, type names, etc.). -/
abbrev Ident := String

-- Binary operators
/-- Supported binary operators in Ziku expressions. -/
inductive BinOp where
  -- Arithmetic
  /-- Addition (+) -/
  | add
  /-- Subtraction (-) -/
  | sub
  /-- Multiplication (*) -/
  | mul
  /-- Division (/) -/
  | div
  -- Comparison
  /-- Equality (==) -/
  | eq
  /-- Inequality (!=) -/
  | ne
  /-- Less than (<) -/
  | lt
  /-- Less than or equal (<=) -/
  | le
  /-- Greater than (>) -/
  | gt
  /-- Greater than or equal (>=) -/
  | ge
  -- Logical
  /-- Logical AND (&&) -/
  | and
  /-- Logical OR (||) -/
  | or
  -- Other
  /-- String/List concatenation (++) -/
  | concat
  /-- Pipe operator (|>) -/
  | pipe
  deriving Repr, BEq, DecidableEq

-- Unary operators
/-- Supported unary operators in Ziku expressions. -/
inductive UnaryOp where
  /-- Negation (-) -/
  | neg   -- -
  /-- Logical NOT (not) -/
  | not   -- not
  deriving Repr, BEq, DecidableEq

-- Built-in functions for string operations
/-- Built-in functions provided by the Ziku runtime. -/
inductive Builtin where
  /-- Returns the length of a string. -/
  | strLen     -- String -> Int
  /-- Returns the character at a given index in a string. -/
  | strAt      -- String -> Int -> Rune
  /-- Returns a substring. -/
  | strSub     -- String -> Int -> Int -> String
  /-- Converts a string to an integer. -/
  | strToInt   -- String -> Int
  /-- Converts an integer to a string. -/
  | intToStr   -- Int -> String
  /-- Converts a rune to a string. -/
  | runeToStr  -- Rune -> String
  /-- Converts an integer to a rune. -/
  | intToRune  -- Int -> Rune
  /-- Converts a rune to an integer. -/
  | runeToInt  -- Rune -> Int
  /-- Reads a line from standard input. -/
  | readLine   -- Unit -> String
  /-- Prints a string to standard output. -/
  | println    -- String -> Unit
  deriving Repr, BEq, DecidableEq

/-- Returns the string representation of a built-in function. -/
def Builtin.toString : Builtin → String
  | .strLen    => "strLen"
  | .strAt     => "strAt"
  | .strSub    => "strSub"
  | .strToInt  => "strToInt"
  | .intToStr  => "intToStr"
  | .runeToStr => "runeToStr"
  | .intToRune => "intToRune"
  | .runeToInt => "runeToInt"
  | .readLine  => "readLine"
  | .println   => "println"

instance : ToString Builtin := ⟨Builtin.toString⟩

-- Literals
/-- Supported literal values in Ziku expressions. -/
inductive Lit where
  /-- Integer literal. -/
  | int    : Int → Lit
  /-- Floating-point literal. -/
  | float  : Float → Lit
  /-- String literal. -/
  | string : String → Lit
  /-- Character (rune) literal. -/
  | char   : Char → Lit
  /-- Boolean literal. -/
  | bool   : Bool → Lit
  /-- Unit literal (). -/
  | unit   : Lit
  deriving Repr, BEq

-- Types
/-- Represents a Ziku type. -/
inductive Ty where
  /-- Type variable (e.g., 'a'). -/
  | var     : SourcePos → Ident → Ty                              -- Type variable: a
  /-- Type constructor (e.g., 'Int', 'Bool'). -/
  | con     : SourcePos → Ident → Ty                              -- Type constructor: Int, Bool
  /-- Type application (e.g., 'List a'). -/
  | app     : SourcePos → Ty → Ty → Ty                            -- Type application: List a
  /-- Function type (e.g., 'a -> b'). -/
  | arrow   : SourcePos → Ty → Ty → Ty                            -- Function type: a -> b
  /-- Polymorphic type (e.g., 'forall a. a -> a'). -/
  | forall_ : SourcePos → Ident → Ty → Ty                         -- Polymorphic: forall a. a -> a
  /-- Record type (e.g., '{ x : Int | r }'). -/
  | record  : SourcePos → List (Ident × Ty) → Option Ty → Ty      -- Record type: { x : Int | ρ }
  /-- Variant type (e.g., '[Cons Int a | Nil | r]'). -/
  | variant : SourcePos → List (Ident × List Ty) → Option Ty → Ty -- Variant type: [Cons Int a | Nil | ρ]
  /-- Bottom type (e.g., '⊥'). -/
  | bottom  : SourcePos → Ty                                      -- Bottom type: ⊥ (never returns)
  /-- Covalue type (e.g., '~T'). -/
  | tilde   : SourcePos → Ty → Ty                                -- Covalue type: ~T
  deriving Repr, BEq

/-- Returns the source position of a type. -/
def Ty.pos : Ty → SourcePos
  | var p _ => p
  | con p _ => p
  | app p _ _ => p
  | arrow p _ _ => p
  | forall_ p _ _ => p
  | record p _ _ => p
  | variant p _ _ => p
  | bottom p => p
  | tilde p _ => p

/-- Returns true if the type is the bottom type. -/
def Ty.isBottom : Ty → Bool
  | bottom _ => true
  | _ => false

-- Patterns (for data destructuring)
/-- Represents a pattern used in match expressions. -/
inductive Pat where
  /-- Variable pattern (e.g., 'x'). -/
  | var     : SourcePos → Ident → Pat                     -- Variable pattern: x
  /-- Literal pattern (e.g., '42'). -/
  | lit     : SourcePos → Lit → Pat                       -- Literal pattern: 42, "hello"
  /-- Wildcard pattern (e.g., '_'). -/
  | wild    : SourcePos → Pat                             -- Wildcard: _
  /-- Constructor pattern (e.g., 'Cons x xs'). -/
  | con     : SourcePos → Ident → List Pat → Pat          -- Constructor: Cons x xs
  /-- Parenthesized pattern (e.g., '(p)'). -/
  | paren   : SourcePos → Pat → Pat                       -- Parenthesized: (p)
  /-- Annotated pattern (e.g., '(p : Ty)'). -/
  | ann     : SourcePos → Pat → Ty → Pat                  -- Annotated: (p : ty)
  deriving Repr, BEq

/-- Returns the source position of a pattern. -/
def Pat.pos : Pat → SourcePos
  | var p _ => p
  | lit p _ => p
  | wild p => p
  | con p _ _ => p
  | paren p _ => p
  | ann p _ _ => p

-- Copattern accessor (for codata construction)
/-- Represents an accessor in a copattern. -/
inductive Accessor where
  /-- Field accessor (e.g., '.field'). -/
  | field : Ident → Accessor                  -- .field
  /-- Application accessor (e.g., '(arg)'). -/
  | apply : Ident → Accessor                  -- (arg)
  deriving Repr, BEq

-- Copattern (sequence of accessors)
-- e.g., #.tail.head becomes [.tail, .head]
-- e.g., #(x) becomes [(x)]
/-- Represents a copattern as a list of accessors. -/
abbrev Copattern := List Accessor

-- Metadata for external declarations
/-- Represents a single external definition entry: (backend, symbol). -/
structure ExternEntry where
  /-- The target platform (e.g., "scheme"). -/
  backend : String
  /-- The symbol name on the target platform. -/
  symbol : String
  /-- Arity of the function (optional). -/
  arity : Option Nat
  deriving Repr, BEq

instance : ToString ExternEntry where
  toString e := 
    match e.arity with
    | some a => s!"@(\"{e.backend}\", \"{e.symbol}\", {a})"
    | none => s!"@(\"{e.backend}\", \"{e.symbol}\")"

/-- Metadata for external declarations is a list of backend entries. -/
abbrev ExternInfo := List ExternEntry

def ExternInfo.toString (info : ExternInfo) : String :=
  String.intercalate " | " (info.map ToString.toString)

-- Expressions
/-- Represents a Ziku expression. -/
inductive Expr where
  /-- Literal value. -/
  | lit       : SourcePos → Lit → Expr                              -- Literal: 42
  /-- Variable. -/
  | var       : SourcePos → Ident → Expr                            -- Variable: x
  /-- Binary operation. -/
  | binOp     : SourcePos → BinOp → Expr → Expr → Expr              -- Binary op: a + b
  /-- Unary operation. -/
  | unaryOp   : SourcePos → UnaryOp → Expr → Expr                   -- Unary op: -x, not p
  /-- Lambda abstraction. -/
  | lam       : SourcePos → Ident → Bool → Expr → Expr              -- Lambda: \x => e
  /-- Function application. -/
  | app       : SourcePos → Expr → Expr → Bool → Expr               -- Application: f x
  /-- Let binding. -/
  | let_      : SourcePos → Ident → Option Ty → Expr → Expr → Expr  -- Let: let x : ty = e in body
  /-- Recursive let binding. -/
  | letRec    : SourcePos → Ident → Option Ty → Expr → Expr → Expr  -- Let rec: let rec f = e in body
  /-- Pattern match expression. -/
  | match_    : SourcePos → Expr → List (Pat × Expr) → Expr         -- Match: match e with | p => e end
  /-- Codata construction block. -/
  | codata    : SourcePos → List (List Pat × Copattern × Expr) → Expr  -- Codata block: { patterns # copat => e, ... }
  /-- Field access. -/
  | field     : SourcePos → Expr → Ident → Expr                     -- Field access: e.field
  /-- Type annotation. -/
  | ann       : SourcePos → Expr → Ty → Expr                        -- Type annotation: (e : ty)
  /-- Anonymous record. -/
  | record    : SourcePos → List (Ident × Expr) → Expr              -- Anonymous record: { x = 1, y = 2 }
  /-- Conditional expression. -/
  | if_       : SourcePos → Expr → Expr → Expr → Expr               -- If: if c then t else f
  /-- Self-reference in codata. -/
  | hash      : SourcePos → Expr                                    -- Self-reference: # (for codata)
  /-- Control label. -/
  | label     : SourcePos → Ident → Expr → Expr                     -- Label: label name { body }
  /-- Jump to label. -/
  | goto      : SourcePos → Expr → Expr → Expr                      -- Goto: goto(expr, covalue_expr)
  /-- Data constructor. -/
  | con       : SourcePos → Ident → List Expr → Expr                -- Constructor: Con args...
  /-- External definition. -/
  | extern    : SourcePos → ExternInfo → Expr                       -- Extern: @("scheme", "foo")
  deriving Repr, BEq

/-- Returns the source position of an expression. -/
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
  | extern p _ => p

-- Data constructor declaration
/-- Represents a declaration of a data constructor. -/
structure ConDecl where
  /-- Name of the constructor. -/
  name : Ident
  /-- Argument types of the constructor. -/
  args : List Ty
  deriving Repr, BEq

-- Codata signature (copattern signature)
/-- Represents a signature for a codata field or method. -/
structure CopatSig where
  /-- Sequence of accessors (copattern). -/
  accessors : Copattern
  /-- Type of the field or method. -/
  ty : Ty
  deriving Repr, BEq

-- Clause for function definition
/-- Represents a clause in a function or method definition. -/
inductive DefClause where
  /-- Pattern matching clause (for data). -/
  | patClause   : List Pat → Expr → DefClause                    -- | p1, p2 => e
  /-- Copattern matching clause (for codata). -/
  | copatClause : List Pat → Copattern → Expr → DefClause        -- p1, p2 #.field => e
  deriving Repr, BEq

-- Top-level declarations
/-- Represents a top-level declaration in Ziku. -/
inductive Decl where
  /-- Data type declaration. -/
  | data    : Ident → List Ident → List ConDecl → Option ExternInfo → Decl          -- data T a = | C1 | C2
  /-- Codata type declaration. -/
  | codata  : Ident → List Ident → List CopatSig → Option ExternInfo → Decl         -- codata T a { #.f : ty }
  /-- Simple function definition. -/
  | def_    : Ident → Ty → Option Expr → Decl                                       -- def f : ty = e
  /-- Function definition with pattern matching. -/
  | defPat  : Ident → Ty → List DefClause → Decl                                    -- def f : ty | p => e
  /-- Infix operator declaration. -/
  | infix_  : Nat → Bool → Ident → Decl                         -- infix 6 ++  (prec, rightAssoc, name)
  /-- Module declaration. -/
  | module_ : Ident → List Decl → Decl                          -- module M where ... end
  /-- Import declaration. -/
  | import_ : Ident → Option (List Ident) → Option Ident → Decl -- import M / import M (a, b) / import M as N
  deriving Repr, BEq

-- A program is a list of declarations
/-- A Ziku program is a list of top-level declarations. -/
abbrev Program := List Decl

-- Helper functions

-- Expression size (manual implementation)
/-- Returns the size of an expression (number of nodes in the AST). -/
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
  | extern _ _ => 1

-- Free variables in an expression
/-- Returns the list of free variables in an expression. -/
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
  | extern _ _ => []


-- Closed expression (no free variables)
/-- Returns true if the expression is closed (has no free variables). -/
def Expr.closed (e : Expr) : Prop := e.freeVars = []

-- Pretty printing helpers
/-- Returns the string representation of a binary operator. -/
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

/-- Returns the string representation of a unary operator. -/
def UnaryOp.toString : UnaryOp → String
  | .neg => "-"
  | .not => "not"

instance : ToString UnaryOp := ⟨UnaryOp.toString⟩

/-- Returns the string representation of a literal value. -/
def Lit.toString : Lit → String
  | .int n => s!"{n}"
  | .float f => s!"{f}"
  | .string s => s!"\"{s}\""
  | .char c => s!"'{c}'"
  | .bool b => if b then "true" else "false"
  | .unit => "()"

instance : ToString Lit := ⟨Lit.toString⟩

-- Pretty print types
/-- Returns the string representation of a type. -/
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
  | .tilde _ t => s!"~{t.toString}"

instance : ToString Ty := ⟨Ty.toString⟩

-- Pretty print patterns
/-- Returns the string representation of a pattern. -/
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
/-- Returns the string representation of an accessor. -/
def Accessor.toString : Accessor → String
  | .field f => s!".{f}"
  | .apply x => s!"({x})"

instance : ToString Accessor := ⟨Accessor.toString⟩

-- Pretty print copattern
/-- Returns the string representation of a copattern. -/
def Copattern.toString (cp : Copattern) : String :=
  String.join (cp.map Accessor.toString)

-- Pretty print expressions
/-- Returns the string representation of an expression. -/
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
      let psStr := if ps.isEmpty then "" else String.intercalate " " (ps.map Pat.toString) ++ " "
      s!"({psStr}#{Copattern.toString cp} => {body.toString})")
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
  | con _ name args =>
    let argsStr := args.map Expr.toString
    s!"(Con \"{name}\" [{String.intercalate ", " argsStr}])"
  | extern _ info => s!"(Extern {ExternInfo.toString info})"

instance : ToString Expr := ⟨Expr.toString⟩

-- Pretty print declarations
/-- Returns the string representation of a top-level declaration. -/
partial def Decl.toString : Decl → String
  | .data name params constrs extern =>
    let ps := if params.isEmpty then "" else " " ++ String.intercalate " " params
    let cs := constrs.map (fun c =>
      let args := if c.args.isEmpty then "" else " " ++ String.intercalate " " (c.args.map Ty.toString)
      s!"| {c.name}{args}")
    let ext := match extern with | some info => s!" = {ExternInfo.toString info}" | none => ""
    s!"(Data {name}{ps} [{String.intercalate " " cs}]{ext})"
  | .codata name params sigs extern =>
    let ps := if params.isEmpty then "" else " " ++ String.intercalate " " params
    let ss := sigs.map (fun s => s!"#{Copattern.toString s.accessors} : {s.ty}")
    let ext := match extern with | some info => s!" = {ExternInfo.toString info}" | none => ""
    s!"(Codata {name}{ps} " ++ "{ " ++ String.intercalate ", " ss ++ " }" ++ s!"{ext})"
  | .def_ name ty body =>
    let bStr := match body with | some b => s!" {b.toString}" | none => ""
    s!"(Def \"{name}\" {ty}{bStr})"
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

import Ziku.Syntax

namespace Ziku.IR

/-!
# Sequent Calculus IR

The intermediate representation is based on the λμμ̃-calculus from
"Grokking the Sequent Calculus" (ICFP 2024).

Three syntactic categories:
- **Producers**: Construct/produce elements of a type
- **Consumers**: Consume/destruct elements of a type
- **Statements**: Drive computation, no return type

Key constructs:
- `μα.s` (mu): Turns a statement into a producer, binding covariable α
- `μ̃x.s` (mu-tilde): Turns a statement into a consumer, binding variable x
- `⟨p | c⟩` (cut): Combines a producer and consumer of the same type
-/

open Ziku (SourcePos Ident BinOp UnaryOp Builtin Lit Ty Pat)

-- Forward declarations for mutual recursion
mutual

-- Producers: construct/produce elements of a type
inductive Producer where
  | var       : SourcePos → Ident → Producer                        -- Variable: x
  | lit       : SourcePos → Lit → Producer                          -- Literal: 42
  | mu        : SourcePos → Ident → Statement → Producer            -- μα.s
  | cocase    : SourcePos → List (Ident × List Ident × Statement) → Producer
      -- cocase { D(x̄; ᾱ) ⇒ s, ... }
      -- Destructor name, argument variables (producer vars), result covars (consumer vars), body
  | record    : SourcePos → List (Ident × Producer) → Producer      -- { x = p, y = q }
  | fix       : SourcePos → Ident → Producer → Producer             -- fix x. p (fixpoint)
  | dataCon   : SourcePos → Ident → List Producer → Producer        -- K(v1, v2, ...) - data constructor
  deriving Repr, BEq

-- Consumers: consume/destruct elements of a type
inductive Consumer where
  | covar     : SourcePos → Ident → Consumer                        -- Covariable: α
  | muTilde   : SourcePos → Ident → Statement → Consumer            -- μ̃x.s
  | case      : SourcePos → List (Ident × List Ident × Statement) → Consumer
      -- case { K(x̄; ᾱ) ⇒ s, ... }
      -- Constructor name, bound variables, body
  | destructor: SourcePos → Ident → List Producer → Consumer → Consumer
      -- D(p̄; c) - apply destructor with arguments and continuation
  deriving Repr, BEq

-- Statements: drive computation
inductive Statement where
  | cut       : SourcePos → Producer → Consumer → Statement         -- ⟨p | c⟩
  | binOp     : SourcePos → BinOp → Producer → Producer → Consumer → Statement
      -- ⊙(p₁, p₂; c) - primitive binary operation
  | ifz       : SourcePos → Producer → Statement → Statement → Statement
      -- ifz(p, s₁, s₂) - conditional on zero/nonzero
  | call      : SourcePos → Ident → List Producer → List Consumer → Statement
      -- f(p̄; c̄) - function/top-level call
  | builtin   : SourcePos → Builtin → List Producer → Consumer → Statement
      -- builtin(p̄; c) - built-in function call (strLen, strAt, etc.)
  deriving Repr, BEq

end

-- Default position for Inhabited instances (not from user code)
def defaultPos : SourcePos := { line := 0, col := 0 }

instance : Inhabited Producer where
  default := .lit defaultPos .unit

instance : Inhabited Consumer where
  default := .covar defaultPos "default"

-- Get source position from Producer
def Producer.pos : Producer → SourcePos
  | var p _ => p
  | lit p _ => p
  | mu p _ _ => p
  | cocase p _ => p
  | record p _ => p
  | fix p _ _ => p
  | dataCon p _ _ => p

-- Get source position from Consumer
def Consumer.pos : Consumer → SourcePos
  | covar p _ => p
  | muTilde p _ _ => p
  | case p _ => p
  | destructor p _ _ _ => p

-- Get source position from Statement
def Statement.pos : Statement → SourcePos
  | cut p _ _ => p
  | binOp p _ _ _ _ => p
  | ifz p _ _ _ => p
  | call p _ _ _ => p
  | builtin p _ _ _ => p

-- Free variables in Producer
mutual
partial def Producer.freeVars : Producer → List Ident
  | .var _ x => [x]
  | .lit _ _ => []
  | .mu _ α s => s.freeVars.filter (· != α)  -- α is a covariable, bound
  | .cocase _ branches =>
    branches.flatMap (fun (_, vars, s) =>
      s.freeVars.filter (fun v => !vars.contains v))
  | .record _ fields => fields.flatMap (fun (_, p) => p.freeVars)
  | .fix _ x body => body.freeVars.filter (· != x)  -- x is bound
  | .dataCon _ _ args => args.flatMap Producer.freeVars

partial def Consumer.freeVars : Consumer → List Ident
  | .covar _ α => [α]
  | .muTilde _ x s => s.freeVars.filter (· != x)
  | .case _ branches =>
    branches.flatMap (fun (_, vars, s) =>
      s.freeVars.filter (fun v => !vars.contains v))
  | .destructor _ _ ps c => ps.flatMap Producer.freeVars ++ c.freeVars

partial def Statement.freeVars : Statement → List Ident
  | .cut _ p c => p.freeVars ++ c.freeVars
  | .binOp _ _ p1 p2 c => p1.freeVars ++ p2.freeVars ++ c.freeVars
  | .ifz _ p s1 s2 => p.freeVars ++ s1.freeVars ++ s2.freeVars
  | .call _ _ ps cs => ps.flatMap Producer.freeVars ++ cs.flatMap Consumer.freeVars
  | .builtin _ _ ps c => ps.flatMap Producer.freeVars ++ c.freeVars
end

-- Pretty printing
mutual
partial def Producer.toString : Producer → String
  | .var _ x => x
  | .lit _ l => s!"{l}"
  | .mu _ α s => s!"(μ{α}. {s.toString})"
  | .cocase _ branches =>
    let bs := branches.map (fun (d, vars, s) =>
      let varsStr := if vars.isEmpty then "" else "(" ++ String.intercalate ", " vars ++ ")"
      s!"{d}{varsStr} ⇒ {s.toString}")
    "cocase { " ++ String.intercalate ", " bs ++ " }"
  | .record _ fields =>
    let fs := fields.map (fun (n, p) => s!"{n} = {p.toString}")
    "{ " ++ String.intercalate ", " fs ++ " }"
  | .fix _ x body => s!"(fix {x}. {body.toString})"
  | .dataCon _ con args =>
    if args.isEmpty then con
    else s!"({con} {String.intercalate " " (args.map Producer.toString)})"

partial def Consumer.toString : Consumer → String
  | .covar _ α => α
  | .muTilde _ x s => s!"(μ~{x}. {s.toString})"
  | .case _ branches =>
    let bs := branches.map (fun (k, vars, s) =>
      let varsStr := if vars.isEmpty then "" else "(" ++ String.intercalate ", " vars ++ ")"
      s!"{k}{varsStr} ⇒ {s.toString}")
    "case { " ++ String.intercalate ", " bs ++ " }"
  | .destructor _ d ps c =>
    let psStr := if ps.isEmpty then "" else "(" ++ String.intercalate ", " (ps.map Producer.toString) ++ ")"
    s!"{d}{psStr}; {c.toString}"

partial def Statement.toString : Statement → String
  | .cut _ p c => s!"⟨{p.toString} | {c.toString}⟩"
  | .binOp _ op p1 p2 c => s!"{op}({p1.toString}, {p2.toString}; {c.toString})"
  | .ifz _ p s1 s2 => s!"ifz({p.toString}, {s1.toString}, {s2.toString})"
  | .call _ f ps cs =>
    let psStr := String.intercalate ", " (ps.map Producer.toString)
    let csStr := String.intercalate ", " (cs.map Consumer.toString)
    s!"{f}({psStr}; {csStr})"
  | .builtin _ b ps c =>
    let psStr := String.intercalate ", " (ps.map Producer.toString)
    s!"{b}({psStr}; {c.toString})"
end

instance : ToString Producer := ⟨Producer.toString⟩
instance : ToString Consumer := ⟨Consumer.toString⟩
instance : ToString Statement := ⟨Statement.toString⟩

-- Top-level definition in IR
structure TopDef where
  name : Ident
  params : List Ident      -- Producer parameters (variables)
  coparams : List Ident    -- Consumer parameters (covariables)
  body : Statement
  deriving Repr, BEq

-- IR Program
abbrev Program := List TopDef

end Ziku.IR

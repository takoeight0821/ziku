import Ziku.IR.Syntax
import Ziku.IR.Eval

set_option linter.missingDocs false

namespace Ziku.IR

/-!
# IR Simplification Pass

Implements administrative redex elimination for the λμμ̃-calculus IR,
following the design from "Grokking the Sequent Calculus" (ICFP 2024).

## Key Reductions (applied only when safe)

```
⟨μα.s | c⟩  →  s[c/α]   (μ-reduction, when c is trivial)
⟨v | μ̃x.s⟩  →  s[v/x]   (μ̃-reduction, when v is trivial)
```

"Trivial" means the term won't cause code explosion when substituted:
- For consumers: covariables (α)
- For producers: variables (x), literals, nullary data constructors

These reductions eliminate administrative redexes at the IR level,
which significantly reduces code size in the generated Scheme output.
-/

open Ziku (SourcePos Ident synthesizedPos)

/-- Check if a consumer is trivial (won't cause code explosion when substituted).
A consumer is trivial if it's just a covariable reference. -/
def Consumer.isTrivial : Consumer → Bool
  | .covar _ _ => true
  | _ => false

/-- Check if a producer is trivial (won't cause code explosion when substituted).
A producer is trivial if it's a variable, literal, or nullary data constructor. -/
def Producer.isTrivial : Producer → Bool
  | .var _ _ => true
  | .lit _ _ => true
  | .dataCon _ _ [] => true  -- Nullary constructor
  | _ => false

mutual

/-- Simplify a producer by eliminating administrative redexes in subterms. -/
partial def Producer.simplify : Producer → Producer
  | .var pos x => .var pos x
  | .lit pos l => .lit pos l
  | .mu pos α s => .mu pos α s.simplify
  | .cocase pos branches =>
    .cocase pos (branches.map fun (d, vars, s) => (d, vars, s.simplify))
  | .record pos fields =>
    .record pos (fields.map fun (n, p) => (n, p.simplify))
  | .fix pos x body => .fix pos x body.simplify
  | .dataCon pos con args => .dataCon pos con (args.map Producer.simplify)

/-- Simplify a consumer by eliminating administrative redexes in subterms. -/
partial def Consumer.simplify : Consumer → Consumer
  | .covar pos α => .covar pos α
  | .muTilde pos x s => .muTilde pos x s.simplify
  | .case pos branches =>
    .case pos (branches.map fun (k, vars, s) => (k, vars, s.simplify))
  | .destructor pos d ps c =>
    .destructor pos d (ps.map Producer.simplify) c.simplify

/-- Simplify a statement by eliminating administrative redexes.

Key reductions (applied only when the substituted term is trivial):
- μ-reduction: ⟨μα.s | c⟩ → s[c/α] (when c is trivial)
- μ̃-reduction: ⟨v | μ̃x.s⟩ → s[v/x] (when v is trivial and a value)
-/
partial def Statement.simplify : Statement → Statement
  | .cut pos p c =>
    match p with
    | .mu _ α s =>
      -- μ-reduction: ⟨μα.s | c⟩ → s[c/α]
      -- Only apply if c is trivial to avoid code explosion
      let c' := c.simplify
      if c'.isTrivial then
        (s.substCovar α c').simplify
      else
        -- c is not trivial, keep the cut but simplify inside
        .cut pos (.mu p.pos α s.simplify) c'
    | _ =>
      match c with
      | .muTilde _ x s =>
        -- μ̃-reduction: ⟨v | μ̃x.s⟩ → s[v/x]
        -- Only apply if p is trivial and a value
        let p' := p.simplify
        if p'.isTrivial && p'.isValue then
          (s.substVar x p').simplify
        else
          -- p is not trivial, keep the cut structure
          .cut pos p' (.muTilde c.pos x s.simplify)
      | _ =>
        -- General case: simplify both sides
        .cut pos p.simplify c.simplify
  | .binOp pos op p1 p2 c =>
    .binOp pos op p1.simplify p2.simplify c.simplify
  | .ifz pos cond s1 s2 =>
    .ifz pos cond.simplify s1.simplify s2.simplify
  | .call pos f ps cs =>
    .call pos f (ps.map Producer.simplify) (cs.map Consumer.simplify)
  | .builtin pos b ps c =>
    .builtin pos b (ps.map Producer.simplify) c.simplify
  | .externalCall pos info ps c =>
    .externalCall pos info (ps.map Producer.simplify) c.simplify

end

/-- Run simplification to a fixed point.

Repeatedly applies simplification until no more changes occur.
The fuel parameter prevents infinite loops in case of bugs.
-/
partial def Statement.simplifyFixpoint (fuel : Nat := 100) (s : Statement) : Statement :=
  if fuel == 0 then s
  else
    let s' := s.simplify
    if s' == s then s
    else s'.simplifyFixpoint (fuel - 1)

/-- Main entry point for simplification.

Applies simplification until reaching a fixed point.
-/
def simplify (s : Statement) : Statement :=
  s.simplifyFixpoint

end Ziku.IR

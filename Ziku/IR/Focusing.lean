import Ziku.Syntax
import Ziku.IR.Syntax

namespace Ziku.IR.Focusing

/-!
# Static Focusing Transformation

Based on "Grokking the Sequent Calculus" (ICFP 2024).

Focusing ensures all subexpressions in value-requiring positions are values.
Non-value producers (like μ-abstractions) are lifted out using μ̃-bindings.

## Key Rules

For constructors with non-value argument:
```
F(K(ps, p, ps')) where p is non-value
= μα.⟨F(p) | μ̃x.⟨F(K(ps, x, ps')) | α⟩⟩
```

For binary operations:
```
F(⊙(p₁, p₂; c)) where p₁ is non-value
= ⟨F(p₁) | μ̃x.F(⊙(x, p₂; c))⟩
```
-/

open Ziku (SourcePos Ident)

-- Focusing monad for fresh variable generation
abbrev FocusM := StateT Nat Id

def freshVar : FocusM Ident := do
  let n ← get
  set (n + 1)
  pure s!"_f{n}"

-- Dummy source position for generated code
def dummyPos : SourcePos := { line := 0, col := 0 }

-- Check if a producer needs focusing (is non-value)
-- A producer needs focusing if it's a μ-abstraction or contains nested non-values
partial def Producer.needsFocus : Producer → Bool
  | .mu _ _ _ => true
  | .dataCon _ _ args => args.any Producer.needsFocus
  | _ => false

mutual
  -- Focus a producer: ensure it's a value by lifting non-values
  partial def focusProducer (p : Producer) : FocusM Producer :=
    match p with
    | .dataCon pos con args => do
      -- Find first non-value argument and lift it
      match args.findIdx? Producer.needsFocus with
      | none =>
        -- All args are values (or don't need focus), recursively process
        let args' ← args.mapM focusProducer
        pure (.dataCon pos con args')
      | some idx =>
        -- Found non-value at idx, lift it
        match args[idx]? with
        | none => pure (.dataCon pos con args)  -- shouldn't happen
        | some nonValueArg =>
          let x ← freshVar
          let α ← freshVar
          let focusedArg ← focusProducer nonValueArg
          let args' := args.set idx (.var dummyPos x)
          -- Recursively focus the rest (may have more non-values)
          let innerDataCon ← focusProducer (.dataCon pos con args')
          -- μα.⟨focusedArg | μ̃x.⟨innerDataCon | α⟩⟩
          pure (.mu dummyPos α (.cut dummyPos focusedArg
            (.muTilde dummyPos x (.cut dummyPos innerDataCon (.covar dummyPos α)))))
    | .mu pos α s => do
      let s' ← focusStatement s
      pure (.mu pos α s')
    | .cocase pos branches => do
      let branches' ← branches.mapM fun (d, vars, s) => do
        let s' ← focusStatement s
        pure (d, vars, s')
      pure (.cocase pos branches')
    | .record pos fields => do
      let fields' ← fields.mapM fun (n, p) => do
        let p' ← focusProducer p
        pure (n, p')
      pure (.record pos fields')
    | .fix pos x body => do
      let body' ← focusProducer body
      pure (.fix pos x body')
    | p => pure p  -- var, lit are already values

  -- Focus a consumer
  partial def focusConsumer (c : Consumer) : FocusM Consumer :=
    match c with
    | .muTilde pos x s => do
      let s' ← focusStatement s
      pure (.muTilde pos x s')
    | .case pos branches => do
      let branches' ← branches.mapM fun (k, vars, s) => do
        let s' ← focusStatement s
        pure (k, vars, s')
      pure (.case pos branches')
    | .destructor pos d ps c => do
      -- Focus producer arguments in destructor
      match ps.findIdx? Producer.needsFocus with
      | none => do
        let ps' ← ps.mapM focusProducer
        let c' ← focusConsumer c
        pure (.destructor pos d ps' c')
      | some idx =>
        match ps[idx]? with
        | none => do
          let c' ← focusConsumer c
          pure (.destructor pos d ps c')
        | some nonValueP =>
          -- μ̃y.⟨F(p) | μ̃x.⟨y | F(D(ps,x,ps';c))⟩⟩
          let y ← freshVar
          let x ← freshVar
          let p ← focusProducer nonValueP
          let ps' := ps.set idx (.var dummyPos x)
          let innerDestr ← focusConsumer (.destructor pos d ps' c)
          pure (.muTilde dummyPos y (.cut dummyPos p
            (.muTilde dummyPos x (.cut dummyPos (.var dummyPos y) innerDestr))))
    | c => pure c  -- covar is already a value

  -- Focus a statement
  partial def focusStatement (s : Statement) : FocusM Statement :=
    match s with
    | .cut pos p c => do
      let p' ← focusProducer p
      let c' ← focusConsumer c
      pure (.cut pos p' c')
    | .binOp pos op p1 p2 c => do
      -- Focus operands left-to-right
      if Producer.needsFocus p1 then
        let x ← freshVar
        let p1' ← focusProducer p1
        let inner ← focusStatement (.binOp pos op (.var dummyPos x) p2 c)
        pure (.cut dummyPos p1' (.muTilde dummyPos x inner))
      else if Producer.needsFocus p2 then
        let x ← freshVar
        let p2' ← focusProducer p2
        let inner ← focusStatement (.binOp pos op p1 (.var dummyPos x) c)
        pure (.cut dummyPos p2' (.muTilde dummyPos x inner))
      else do
        let c' ← focusConsumer c
        pure (.binOp pos op p1 p2 c')
    | .ifz pos cond s1 s2 => do
      if Producer.needsFocus cond then
        let x ← freshVar
        let cond' ← focusProducer cond
        let inner ← focusStatement (.ifz pos (.var dummyPos x) s1 s2)
        pure (.cut dummyPos cond' (.muTilde dummyPos x inner))
      else do
        let s1' ← focusStatement s1
        let s2' ← focusStatement s2
        pure (.ifz pos cond s1' s2')
    | .builtin pos b ps c => do
      -- Focus all producer arguments
      match ps.findIdx? Producer.needsFocus with
      | none => do
        let c' ← focusConsumer c
        pure (.builtin pos b ps c')
      | some idx =>
        match ps[idx]? with
        | none => do
          let c' ← focusConsumer c
          pure (.builtin pos b ps c')
        | some nonValueP =>
          let x ← freshVar
          let p ← focusProducer nonValueP
          let ps' := ps.set idx (.var dummyPos x)
          let inner ← focusStatement (.builtin pos b ps' c)
          pure (.cut dummyPos p (.muTilde dummyPos x inner))
    | .call pos f ps cs => do
      match ps.findIdx? Producer.needsFocus with
      | none => do
        let cs' ← cs.mapM focusConsumer
        pure (.call pos f ps cs')
      | some idx =>
        match ps[idx]? with
        | none => do
          let cs' ← cs.mapM focusConsumer
          pure (.call pos f ps cs')
        | some nonValueP =>
          let x ← freshVar
          let p ← focusProducer nonValueP
          let ps' := ps.set idx (.var dummyPos x)
          let inner ← focusStatement (.call pos f ps' cs)
          pure (.cut dummyPos p (.muTilde dummyPos x inner))
end

-- Main entry point: apply focusing transformation to a statement
def focus (s : Statement) : Statement :=
  (focusStatement s).run' 0

end Ziku.IR.Focusing

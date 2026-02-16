import Ziku.IR.Syntax

set_option linter.missingDocs false

namespace Ziku.Proofs.IR

/-!
# Substitution Relations for IR

This module defines substitution as inductive relations, formalizing the
six `partial def` substitution functions from `Ziku/IR/Eval.lean`:

| Proof Relation    | Implementation (IR/Eval.lean) |
|-------------------|-------------------------------|
| `SubstVarProd`    | `Producer.substVar` (58-72)   |
| `SubstVarCons`    | `Consumer.substVar` (74-84)   |
| `SubstVarStmt`    | `Statement.substVar` (86-92)  |
| `SubstCovarProd`  | `Producer.substCovar` (97-110)|
| `SubstCovarCons`  | `Consumer.substCovar` (112-120)|
| `SubstCovarStmt`  | `Statement.substCovar` (122-128)|

## Why Relations Instead of Functions?

The original implementation uses `partial def` because:
1. Mutual recursion through complex data structures
2. Lean cannot prove termination automatically

By defining substitution as relations, we can:
1. Use them in proofs without partiality issues
2. State and prove properties about substitution
3. The relations are total by construction (as Prop)
-/

open Ziku (SourcePos Ident Lit BinOp Builtin ExternInfo)
open Ziku.IR (Producer Consumer Statement)

/-!
## Variable Substitution

`SubstVar x p e e'` means substituting producer `p` for variable `x` in `e` yields `e'`.
All mutually recursive types must be in the same `mutual` block.
-/

mutual
/-- Variable substitution in producers. -/
inductive SubstVarProd : Ident → Producer → Producer → Producer → Prop where
  | var_eq : ∀ x p pos, SubstVarProd x p (.var pos x) p
  | var_neq : ∀ x y p pos, x ≠ y → SubstVarProd x p (.var pos y) (.var pos y)
  | lit : ∀ x p pos l, SubstVarProd x p (.lit pos l) (.lit pos l)
  | mu : ∀ x p pos α s s', SubstVarStmt x p s s' → SubstVarProd x p (.mu pos α s) (.mu pos α s')
  | cocase : ∀ x p pos branches branches',
      SubstVarBranches x p branches branches' →
      SubstVarProd x p (.cocase pos branches) (.cocase pos branches')
  | record : ∀ x p pos fields fields',
      SubstVarFields x p fields fields' →
      SubstVarProd x p (.record pos fields) (.record pos fields')
  | fix_bound : ∀ x p pos body, SubstVarProd x p (.fix pos x body) (.fix pos x body)
  | fix_free : ∀ x y p pos body body',
      x ≠ y → SubstVarProd x p body body' → SubstVarProd x p (.fix pos y body) (.fix pos y body')
  | dataCon : ∀ x p pos con args args',
      SubstVarArgs x p args args' → SubstVarProd x p (.dataCon pos con args) (.dataCon pos con args')

/-- Variable substitution in consumers. -/
inductive SubstVarCons : Ident → Producer → Consumer → Consumer → Prop where
  | covar : ∀ x p pos α, SubstVarCons x p (.covar pos α) (.covar pos α)
  | muTilde_bound : ∀ x p pos s, SubstVarCons x p (.muTilde pos x s) (.muTilde pos x s)
  | muTilde_free : ∀ x y p pos s s',
      x ≠ y → SubstVarStmt x p s s' → SubstVarCons x p (.muTilde pos y s) (.muTilde pos y s')
  | case : ∀ x p pos branches branches',
      SubstVarCaseBranches x p branches branches' →
      SubstVarCons x p (.case pos branches) (.case pos branches')
  | destructor : ∀ x p pos d ps ps' c c',
      SubstVarArgs x p ps ps' → SubstVarCons x p c c' →
      SubstVarCons x p (.destructor pos d ps c) (.destructor pos d ps' c')

/-- Variable substitution in statements. -/
inductive SubstVarStmt : Ident → Producer → Statement → Statement → Prop where
  | cut : ∀ x p pos prod prod' cons cons',
      SubstVarProd x p prod prod' → SubstVarCons x p cons cons' →
      SubstVarStmt x p (.cut pos prod cons) (.cut pos prod' cons')
  | binOp : ∀ x p pos op p1 p1' p2 p2' cons cons',
      SubstVarProd x p p1 p1' → SubstVarProd x p p2 p2' → SubstVarCons x p cons cons' →
      SubstVarStmt x p (.binOp pos op p1 p2 cons) (.binOp pos op p1' p2' cons')
  | ifz : ∀ x p pos cond cond' s1 s1' s2 s2',
      SubstVarProd x p cond cond' → SubstVarStmt x p s1 s1' → SubstVarStmt x p s2 s2' →
      SubstVarStmt x p (.ifz pos cond s1 s2) (.ifz pos cond' s1' s2')
  | call : ∀ x p pos f ps ps' cs cs',
      SubstVarArgs x p ps ps' → SubstVarConsArgs x p cs cs' →
      SubstVarStmt x p (.call pos f ps cs) (.call pos f ps' cs')
  | builtin : ∀ x p pos b ps ps' cons cons',
      SubstVarArgs x p ps ps' → SubstVarCons x p cons cons' →
      SubstVarStmt x p (.builtin pos b ps cons) (.builtin pos b ps' cons')
  | externalCall : ∀ x p pos info ps ps' cons cons',
      SubstVarArgs x p ps ps' → SubstVarCons x p cons cons' →
      SubstVarStmt x p (.externalCall pos info ps cons) (.externalCall pos info ps' cons')

/-- Substitution in a list of producer arguments -/
inductive SubstVarArgs : Ident → Producer → List Producer → List Producer → Prop where
  | nil : ∀ x p, SubstVarArgs x p [] []
  | cons : ∀ x p arg arg' args args',
      SubstVarProd x p arg arg' → SubstVarArgs x p args args' →
      SubstVarArgs x p (arg :: args) (arg' :: args')

/-- Substitution in a list of consumer arguments -/
inductive SubstVarConsArgs : Ident → Producer → List Consumer → List Consumer → Prop where
  | nil : ∀ x p, SubstVarConsArgs x p [] []
  | cons : ∀ x p c c' cs cs',
      SubstVarCons x p c c' → SubstVarConsArgs x p cs cs' →
      SubstVarConsArgs x p (c :: cs) (c' :: cs')

/-- Substitution in cocase branches -/
inductive SubstVarBranches : Ident → Producer → List (Ident × List Ident × Statement) → List (Ident × List Ident × Statement) → Prop where
  | nil : ∀ x p, SubstVarBranches x p [] []
  | cons_bound : ∀ x p d vars s branches branches',
      x ∈ vars → SubstVarBranches x p branches branches' →
      SubstVarBranches x p ((d, vars, s) :: branches) ((d, vars, s) :: branches')
  | cons_free : ∀ x p d vars s s' branches branches',
      x ∉ vars → SubstVarStmt x p s s' → SubstVarBranches x p branches branches' →
      SubstVarBranches x p ((d, vars, s) :: branches) ((d, vars, s') :: branches')

/-- Substitution in case branches -/
inductive SubstVarCaseBranches : Ident → Producer → List (Ident × List Ident × Statement) → List (Ident × List Ident × Statement) → Prop where
  | nil : ∀ x p, SubstVarCaseBranches x p [] []
  | cons_bound : ∀ x p k vars s branches branches',
      x ∈ vars → SubstVarCaseBranches x p branches branches' →
      SubstVarCaseBranches x p ((k, vars, s) :: branches) ((k, vars, s) :: branches')
  | cons_free : ∀ x p k vars s s' branches branches',
      x ∉ vars → SubstVarStmt x p s s' → SubstVarCaseBranches x p branches branches' →
      SubstVarCaseBranches x p ((k, vars, s) :: branches) ((k, vars, s') :: branches')

/-- Substitution in record fields -/
inductive SubstVarFields : Ident → Producer → List (Ident × Producer) → List (Ident × Producer) → Prop where
  | nil : ∀ x p, SubstVarFields x p [] []
  | cons : ∀ x p n prod prod' fields fields',
      SubstVarProd x p prod prod' → SubstVarFields x p fields fields' →
      SubstVarFields x p ((n, prod) :: fields) ((n, prod') :: fields')
end

/-!
## Covariable Substitution

`SubstCovar α c e e'` means substituting consumer `c` for covariable `α` in `e` yields `e'`.
-/

mutual
/-- Covariable substitution in producers. -/
inductive SubstCovarProd : Ident → Consumer → Producer → Producer → Prop where
  | var : ∀ α c pos x, SubstCovarProd α c (.var pos x) (.var pos x)
  | lit : ∀ α c pos l, SubstCovarProd α c (.lit pos l) (.lit pos l)
  | mu_bound : ∀ α c pos s, SubstCovarProd α c (.mu pos α s) (.mu pos α s)
  | mu_free : ∀ α β c pos s s',
      α ≠ β → SubstCovarStmt α c s s' → SubstCovarProd α c (.mu pos β s) (.mu pos β s')
  | cocase : ∀ α c pos branches branches',
      SubstCovarBranches α c branches branches' →
      SubstCovarProd α c (.cocase pos branches) (.cocase pos branches')
  | record : ∀ α c pos fields fields',
      SubstCovarFields α c fields fields' →
      SubstCovarProd α c (.record pos fields) (.record pos fields')
  | fix : ∀ α c pos y body body',
      SubstCovarProd α c body body' → SubstCovarProd α c (.fix pos y body) (.fix pos y body')
  | dataCon : ∀ α c pos con args args',
      SubstCovarProdArgs α c args args' →
      SubstCovarProd α c (.dataCon pos con args) (.dataCon pos con args')

/-- Covariable substitution in consumers. -/
inductive SubstCovarCons : Ident → Consumer → Consumer → Consumer → Prop where
  | covar_eq : ∀ α c pos, SubstCovarCons α c (.covar pos α) c
  | covar_neq : ∀ α β c pos, α ≠ β → SubstCovarCons α c (.covar pos β) (.covar pos β)
  | muTilde : ∀ α c pos x s s',
      SubstCovarStmt α c s s' → SubstCovarCons α c (.muTilde pos x s) (.muTilde pos x s')
  | case : ∀ α c pos branches branches',
      SubstCovarCaseBranches α c branches branches' →
      SubstCovarCons α c (.case pos branches) (.case pos branches')
  | destructor : ∀ α c pos d ps ps' c' c'',
      SubstCovarProdArgs α c ps ps' → SubstCovarCons α c c' c'' →
      SubstCovarCons α c (.destructor pos d ps c') (.destructor pos d ps' c'')

/-- Covariable substitution in statements. -/
inductive SubstCovarStmt : Ident → Consumer → Statement → Statement → Prop where
  | cut : ∀ α c pos prod prod' cons cons',
      SubstCovarProd α c prod prod' → SubstCovarCons α c cons cons' →
      SubstCovarStmt α c (.cut pos prod cons) (.cut pos prod' cons')
  | binOp : ∀ α c pos op p1 p1' p2 p2' cons cons',
      SubstCovarProd α c p1 p1' → SubstCovarProd α c p2 p2' → SubstCovarCons α c cons cons' →
      SubstCovarStmt α c (.binOp pos op p1 p2 cons) (.binOp pos op p1' p2' cons')
  | ifz : ∀ α c pos cond cond' s1 s1' s2 s2',
      SubstCovarProd α c cond cond' → SubstCovarStmt α c s1 s1' → SubstCovarStmt α c s2 s2' →
      SubstCovarStmt α c (.ifz pos cond s1 s2) (.ifz pos cond' s1' s2')
  | call : ∀ α c pos f ps ps' cs cs',
      SubstCovarProdArgs α c ps ps' → SubstCovarConsArgs α c cs cs' →
      SubstCovarStmt α c (.call pos f ps cs) (.call pos f ps' cs')
  | builtin : ∀ α c pos b ps ps' cons cons',
      SubstCovarProdArgs α c ps ps' → SubstCovarCons α c cons cons' →
      SubstCovarStmt α c (.builtin pos b ps cons) (.builtin pos b ps' cons')
  | externalCall : ∀ α c pos info ps ps' cons cons',
      SubstCovarProdArgs α c ps ps' → SubstCovarCons α c cons cons' →
      SubstCovarStmt α c (.externalCall pos info ps cons) (.externalCall pos info ps' cons')

/-- Substitution in a list of producer arguments -/
inductive SubstCovarProdArgs : Ident → Consumer → List Producer → List Producer → Prop where
  | nil : ∀ α c, SubstCovarProdArgs α c [] []
  | cons : ∀ α c arg arg' args args',
      SubstCovarProd α c arg arg' → SubstCovarProdArgs α c args args' →
      SubstCovarProdArgs α c (arg :: args) (arg' :: args')

/-- Substitution in a list of consumer arguments -/
inductive SubstCovarConsArgs : Ident → Consumer → List Consumer → List Consumer → Prop where
  | nil : ∀ α c, SubstCovarConsArgs α c [] []
  | cons : ∀ α c con con' cs cs',
      SubstCovarCons α c con con' → SubstCovarConsArgs α c cs cs' →
      SubstCovarConsArgs α c (con :: cs) (con' :: cs')

/-- Substitution in cocase branches -/
inductive SubstCovarBranches : Ident → Consumer → List (Ident × List Ident × Statement) → List (Ident × List Ident × Statement) → Prop where
  | nil : ∀ α c, SubstCovarBranches α c [] []
  | cons_bound : ∀ α c d vars s branches branches',
      α ∈ vars → SubstCovarBranches α c branches branches' →
      SubstCovarBranches α c ((d, vars, s) :: branches) ((d, vars, s) :: branches')
  | cons_free : ∀ α c d vars s s' branches branches',
      α ∉ vars → SubstCovarStmt α c s s' → SubstCovarBranches α c branches branches' →
      SubstCovarBranches α c ((d, vars, s) :: branches) ((d, vars, s') :: branches')

/-- Substitution in case branches -/
inductive SubstCovarCaseBranches : Ident → Consumer → List (Ident × List Ident × Statement) → List (Ident × List Ident × Statement) → Prop where
  | nil : ∀ α c, SubstCovarCaseBranches α c [] []
  | cons_bound : ∀ α c k vars s branches branches',
      α ∈ vars → SubstCovarCaseBranches α c branches branches' →
      SubstCovarCaseBranches α c ((k, vars, s) :: branches) ((k, vars, s) :: branches')
  | cons_free : ∀ α c k vars s s' branches branches',
      α ∉ vars → SubstCovarStmt α c s s' → SubstCovarCaseBranches α c branches branches' →
      SubstCovarCaseBranches α c ((k, vars, s) :: branches) ((k, vars, s') :: branches')

/-- Substitution in record fields -/
inductive SubstCovarFields : Ident → Consumer → List (Ident × Producer) → List (Ident × Producer) → Prop where
  | nil : ∀ α c, SubstCovarFields α c [] []
  | cons : ∀ α c n prod prod' fields fields',
      SubstCovarProd α c prod prod' → SubstCovarFields α c fields fields' →
      SubstCovarFields α c ((n, prod) :: fields) ((n, prod') :: fields')
end

/-!
## Basic Lemmas
-/

/-- Variable substitution is deterministic for literals. -/
theorem SubstVarProd.lit_deterministic : ∀ x p pos l result,
    SubstVarProd x p (.lit pos l) result → result = .lit pos l := by
  intro x p pos l result h
  cases h
  rfl

/-- Substitution preserves itself when variable doesn't occur -/
theorem SubstVarProd.id_lit : ∀ x p pos l,
    SubstVarProd x p (.lit pos l) (.lit pos l) := SubstVarProd.lit

/-- Variable substitution on a variable either replaces or preserves. -/
theorem SubstVarProd.var_cases : ∀ x p pos y result,
    SubstVarProd x p (.var pos y) result →
    (x = y ∧ result = p) ∨ (x ≠ y ∧ result = .var pos y) := by
  intro x p pos y result h
  cases h
  case var_eq => left; exact ⟨rfl, rfl⟩
  case var_neq hneq => right; exact ⟨hneq, rfl⟩

end Ziku.Proofs.IR

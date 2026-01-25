---
description: Write proofs in Lean 4 for Ziku. Use when user asks to "prove", "add a lemma", "verify property", "formalize", or when modifying files in Ziku/Proofs/.
---

# Proof Writing for Ziku

Guidelines for writing proofs in the Ziku codebase.

## Proofs Directory Structure

```
Ziku/Proofs/
├── Arithmetic.lean    -- Arithmetic operation properties
├── Eval.lean          -- Evaluation properties
├── Identities.lean    -- Basic identities
├── Soundness.lean     -- Type soundness (limited by partial)
└── IR/
    ├── Evaluation.lean   -- IR evaluation properties
    ├── Semantics.lean    -- Operational semantics
    ├── Substitution.lean -- Substitution lemmas
    └── Values.lean       -- Value properties
```

## The `partial` Limitation

**Critical**: Functions marked `partial` cannot be used in proofs.

```lean
-- This is marked partial
partial def eval (stmt : Statement) : IO Value := ...

-- Therefore, you CANNOT prove properties about eval directly
-- ❌ theorem eval_deterministic : eval s₁ = eval s₂ → s₁ = s₂ := by ...
```

### Workarounds

1. **Fuel-based version for proofs**:
   ```lean
   -- Define a fuel-based version
   def evalFuel (fuel : Nat) (stmt : Statement) : Option Value := ...

   -- Prove properties about evalFuel
   theorem evalFuel_deterministic (h : evalFuel n s = some v₁)
       (h' : evalFuel n s = some v₂) : v₁ = v₂ := by ...
   ```

2. **Step-based small-step semantics**:
   ```lean
   -- Define single-step reduction
   inductive Step : Statement → Statement → Prop where
     | mu_reduce : Step (cut (mu α s) c) (s.substCovar α c)
     | ...

   -- Prove properties about Step
   theorem step_deterministic (h₁ : Step s s₁) (h₂ : Step s s₂) : s₁ = s₂ := by ...
   ```

3. **Prove properties about syntax/substitution** (no `partial` involved):
   ```lean
   -- Substitution doesn't use partial
   theorem subst_twice (x : String) (p q : Producer) (prod : Producer) :
       (prod.substVar x p).substVar x q = prod.substVar x q := by ...
   ```

## Proof Style Guidelines

### Use Tactic Proofs

```lean
-- ✅ Preferred: Tactic proof
theorem lookup_some_mem (h : l.lookup k = some v) :
    k ∈ l.map Prod.fst := by
  induction l with
  | nil => simp [List.lookup] at h
  | cons head tail ih =>
    simp [List.lookup] at h
    split at h
    · rename_i heq
      simp [List.mem_map]
      left
      exact LawfulBEq.eq_of_beq heq
    · right
      exact ih h

-- ⚠️ Term-mode proofs are acceptable for simple cases
theorem trivial_id : ∀ x, x = x := fun _ => rfl
```

### Structure Complex Proofs

```lean
theorem complex_property : P := by
  -- Step 1: Establish preconditions
  have h1 : Q := by
    ...

  -- Step 2: Apply main lemma
  have h2 : R := main_lemma h1

  -- Step 3: Conclude
  exact final_step h2
```

### Use `sorry` Carefully

```lean
-- ✅ OK during development, with explanation
theorem wip_property : P := by
  sorry -- TODO: Need to prove Q first, see issue #123

-- ❌ Never commit sorry without explanation
theorem mystery : P := by
  sorry
```

## Common Proof Patterns

### Induction on AST

```lean
theorem subst_preserves (p : Producer) :
    P (p.substVar x q) := by
  induction p with
  | var name =>
    simp [Producer.substVar]
    split <;> simp [*]
  | cut prod cons ih_prod ih_cons =>
    simp [Producer.substVar]
    constructor
    · exact ih_prod
    · exact ih_cons
  | ...
```

### Case Analysis

```lean
theorem eval_progress (stmt : Statement) :
    IsValue stmt ∨ ∃ stmt', Step stmt stmt' := by
  cases stmt with
  | cut prod cons =>
    cases prod with
    | var x => ...
    | mu α s => right; exact ⟨s.substCovar α cons, Step.mu_reduce⟩
    | ...
```

### Decidability

```lean
instance : DecidableEq Producer := by
  intro p₁ p₂
  cases p₁ <;> cases p₂ <;>
    try { right; intro h; injection h }
  all_goals {
    rename_i a b
    exact if h : a = b then isTrue (by subst h; rfl)
          else isFalse (by intro heq; injection heq; contradiction)
  }
```

## Verification Checklist

Before committing proofs:

- [ ] No `sorry` without explanation
- [ ] All theorems have meaningful names
- [ ] Complex proofs are commented
- [ ] `#check` succeeds for all theorems
- [ ] Build succeeds: `lake build`

After modifying `Ziku/Proofs/`:

```bash
# Verify no sorry in committed code
grep -r "sorry" Ziku/Proofs/

# Ensure build succeeds
docker run --rm ziku lake build
```

## Naming Conventions

| Kind | Pattern | Example |
|------|---------|---------|
| Lemma (helper) | `{property}_aux` | `subst_preserves_aux` |
| Main theorem | `{subject}_{property}` | `eval_deterministic` |
| Inverse | `{name}_inv` | `lookup_mem_inv` |
| Composition | `{name}_comp` | `subst_comp` |

## References

- [Ziku/Proofs/](../../Ziku/Proofs/) - Existing proofs
- [CLAUDE.md#verification-checklist](../../CLAUDE.md) - Verification requirements
- [/lean4-conventions](../lean4-conventions/SKILL.md) - Lean 4 coding conventions

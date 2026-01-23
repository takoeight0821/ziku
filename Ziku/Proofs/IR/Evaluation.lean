import Ziku.Proofs.IR.Semantics

set_option linter.missingDocs false

namespace Ziku.Proofs.IR

/-!
# Multi-Step Evaluation Properties

This module provides additional properties and lemmas about multi-step evaluation.
The `Steps` relation is defined in `Semantics.lean` as the reflexive-transitive
closure of `Step`.

## Correspondence with Implementation

| Proof Relation | Implementation (IR/Eval.lean) |
|----------------|-------------------------------|
| `Steps`        | `evalWithFuel` (430-448)      |
| `Evaluates`    | `eval` (451)                  |

The key difference is that the implementation uses a fuel parameter to ensure
termination, while the proof uses an inductive relation that may not terminate
but is well-defined as a proposition.
-/

open Ziku (SourcePos Ident Lit)
open Ziku.IR (Producer Consumer Statement)

/-- A statement evaluates to a value if it reduces to a cut with halt.
    This corresponds to normal termination in `evalWithFuel`. -/
def Evaluates (s : Statement) (v : Producer) : Prop :=
  ∃ vpos, Steps s (.cut vpos v (.covar vpos "halt"))

/-- A statement is stuck if it cannot step and is not a final value.
    Corresponds to `EvalResult.stuck` in the implementation. -/
def Stuck (s : Statement) : Prop :=
  ¬(∃ s', Step s s') ∧ ¬(∃ pos v, s = .cut pos v (.covar pos "halt") ∧ IsValue v)

/-- A statement terminates if it either evaluates to a value or gets stuck. -/
def Terminates (s : Statement) : Prop :=
  (∃ v, Evaluates s v) ∨ (∃ s', Steps s s' ∧ Stuck s')

-- Composition lemmas

/-- If s1 reduces to s2 and s2 evaluates to v, then s1 evaluates to v. -/
theorem Evaluates.of_steps : ∀ s1 s2 v,
    Steps s1 s2 → Evaluates s2 v → Evaluates s1 v := by
  intro s1 s2 v hsteps heval
  obtain ⟨vpos, hsteps'⟩ := heval
  exact ⟨vpos, Steps.trans s1 s2 _ hsteps hsteps'⟩

/-- Evaluates is preserved under single step backward. -/
theorem Evaluates.of_step : ∀ s1 s2 v,
    Step s1 s2 → Evaluates s2 v → Evaluates s1 v := by
  intro s1 s2 v hstep heval
  exact Evaluates.of_steps s1 s2 v (Step.toSteps s1 s2 hstep) heval

-- Determinism lemmas (partial)

/-- If a statement is stuck, it doesn't step. -/
theorem Stuck.no_step : ∀ s, Stuck s → ¬(∃ s', Step s s') := by
  intro s ⟨hno_step, _⟩
  exact hno_step

-- Normal forms

/-- A statement is in normal form if it cannot step. -/
def NormalForm (s : Statement) : Prop :=
  ¬(∃ s', Step s s')

/-- A statement is a final value if it's a cut with halt and a value. -/
def IsFinal (s : Statement) : Prop :=
  ∃ pos v, s = .cut pos v (.covar pos "halt") ∧ IsValue v

/-- Literals at halt are final. -/
theorem lit_halt_is_final : ∀ pos l, IsFinal (.cut pos (.lit pos l) (.covar pos "halt")) := by
  intro pos l
  exact ⟨pos, .lit pos l, rfl, IsValue.lit pos l⟩

/-- Records at halt are final. -/
theorem record_halt_is_final : ∀ pos fields,
    IsFinal (.cut pos (.record pos fields) (.covar pos "halt")) := by
  intro pos fields
  exact ⟨pos, .record pos fields, rfl, IsValue.record pos fields⟩

/-- Cocase at halt is final. -/
theorem cocase_halt_is_final : ∀ pos branches,
    IsFinal (.cut pos (.cocase pos branches) (.covar pos "halt")) := by
  intro pos branches
  exact ⟨pos, .cocase pos branches, rfl, IsValue.cocase pos branches⟩

end Ziku.Proofs.IR

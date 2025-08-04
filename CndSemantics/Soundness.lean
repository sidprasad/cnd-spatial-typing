import Mathlib.Data.Finset.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Tactic
import CndSemantics.Definitions

namespace CnD

--------------------------------------------------------------------------------
-- Core definitions
--------------------------------------------------------------------------------

abbrev ConstraintSet := Finset Constraint

/-- One dynamic step: add a constraint. -/
inductive Step : ConstraintSet → ConstraintSet → Prop
| add (Γ : ConstraintSet) (C : Constraint) : Step Γ (Γ ∪ {C})

/-- A realization satisfies all constraints in Γ. -/
def satisfies_all (R : Realization) (Γ : ConstraintSet) : Prop :=
  ∀ C ∈ Γ, satisfies R C

/-- Models(Γ) is the set of all realizations satisfying Γ. -/
def models (Γ : ConstraintSet) : Set Realization :=
  { R | satisfies_all R Γ }

/-- Γ is satisfiable iff there exists some realization in its model set. -/
def satisfiable (Γ : ConstraintSet) : Prop :=
  ∃ R, R ∈ models Γ

--------------------------------------------------------------------------------
-- Refinement, Progress, Preservation
--------------------------------------------------------------------------------

/-- Adding a constraint refines (shrinks) the set of models. -/
theorem refinement (Γ : ConstraintSet) (C : Constraint) :
    models (Γ ∪ {C} : Finset Constraint) ⊆ models Γ := by
  intro R h
  unfold models satisfies_all at *
  intro D hD
  exact h D (Finset.mem_union_left {C} hD)

/-- Progress: a satisfiable constraint set has at least one model. -/
theorem progress (Γ : ConstraintSet) :
    satisfiable Γ → ∃ R, R ∈ models Γ := by
  intro h; simpa [satisfiable] using h

/-- Preservation: if Γ ⟶ Γ' and R ∈ models Γ', then R ∈ models Γ. -/
theorem preservation {Γ Γ' : ConstraintSet} {R : Realization} :
    Step Γ Γ' → R ∈ models Γ' → R ∈ models Γ := by
  intro hStep hR
  cases hStep with
  | add Γ C =>
    unfold models satisfies_all at *
    intro D hD
    apply hR
    exact Finset.mem_union_left {C} hD

--------------------------------------------------------------------------------
-- Soundness
--------------------------------------------------------------------------------

open Relation

/-- Soundness: every reachable satisfiable Γ has a model. -/
theorem soundness_reachable :
    ∀ {Γ : ConstraintSet}, ReflTransGen Step ∅ Γ → satisfiable Γ → ∃ R, R ∈ models Γ := by
  intro Γ hSteps hSat
  induction hSteps with
  | refl =>
    -- base: Γ = ∅
    exact progress ∅ hSat
  | tail Γ Δ hSteps ih hStep =>
    -- step: Γ ⟶ Δ
    obtain ⟨R, hR⟩ := progress Δ hSat
    have hPres := preservation hStep hR
    exact ⟨R, hPres⟩

--------------------------------------------------------------------------------
-- Unsatisfiability
--------------------------------------------------------------------------------

/-- A constraint set is unsatisfiable iff its model set is empty. -/
theorem unsat_iff_empty_models (Γ : ConstraintSet) :
    ¬ satisfiable Γ ↔ models Γ = ∅ := by
  constructor
  · intro h
    ext R
    simp [satisfiable, models] at *
    intro hR
    exact h ⟨R, hR⟩
  · intro h1 h2
    simp [satisfiable, models] at *
    obtain ⟨R, hR⟩ := h2
    have : R ∈ (∅ : Set Realization) := by rw [←h1]; exact hR
    contradiction

end CnD

import CndSemantics.Definitions

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Real.Basic

namespace CnD


-- Programs : Constraint sets



-- TODO: NO overlapping boxes in a Realization.




def well_typed (Γ : Finset Constraint) (R : Realization) : Prop :=
  ∀ C ∈ Γ, satisfies R C

abbrev ConstraintSet := Finset Constraint
def satisfies_all (R : Realization) (S : ConstraintSet) : Prop :=
  ∀ c ∈ S, satisfies R c

def models (S : ConstraintSet) : Set Realization :=
  { R | satisfies_all R S }


-- By definition: satisfiable sets have at least one realization.
def satisfiable (S : ConstraintSet) : Prop :=
  ∃ R : Realization, satisfies_all R S





theorem refinement (S : Finset Constraint) (C : Constraint) :
  models (S ∪ ({C} : Finset Constraint)) ⊆ models S := by
  intro R h
  unfold models satisfies_all at *
  simp_all


---

-- realizations are preserved when constraints they satisfy are added.
theorem preservation (S : ConstraintSet) (C : Constraint) (R : Realization) :
  R ∈ models S → satisfies R C → R ∈ models (S ∪ {C}) := by
  intro h hC
  unfold models satisfies_all at *
  intro C' hC'
  cases Finset.mem_union.mp hC' with
  | inl hS => exact h _ hS
  | inr hSingleton =>
    have : C' = C := by simpa using hSingleton
    rw [this]; exact hC




---

theorem unsat_models_empty (S : ConstraintSet) :
  ¬ satisfiable S ↔ models S = ∅ := by
  constructor
  · intro h
    ext R
    simp [models, satisfiable] at *
    intro hR
    sorry




-- we want a theorem that says IF unsat, then by refinement R goes to empty set





end CnD

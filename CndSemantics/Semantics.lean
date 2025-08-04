import CndSemantics.Definitions

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Real.Basic

namespace Semantics
open CnD
/--
* C
* Realization `R` = (a concrete placement of atoms that satisfies a set of spatial constraints).
-/

/- Constraint set `Γ` = a program/specification.-/
abbrev ConstraintSet := Finset Constraint
def satisfies_all (R : Realization) (S : ConstraintSet) : Prop :=
  ∀ c ∈ S, satisfies R c



def models (S : ConstraintSet) : Set Realization :=
  { R | satisfies_all R S }

/--
  $$
  \llbracket Γ \rrbracket = \{ R \mid ∀ C ∈ Γ, \; R \models C \}
  $$

  The denotation of `Γ` is the set of all realizations that satisfy its constraints.
-/



-- By definition: satisfiable sets have at least one realization.
def satisfiable (S : ConstraintSet) : Prop :=
  ∃ R : Realization, satisfies_all R S




/--

Adding a new constraint narrows the set of models:

  $$
  \llbracket Γ ∪ \{C\} \rrbracket \subseteq \llbracket Γ \rrbracket
  $$

-/
theorem refinement (S : Finset Constraint) (C : Constraint) :
  models (S ∪ ({C} : Finset Constraint)) ⊆ models S := by
  intro R h
  unfold models satisfies_all at *
  simp_all




-- Widening: Removing a constraint widens the set of models
theorem widening (S : ConstraintSet) (C : Constraint) :
  models (S \ {C}) ⊇ models S := by
  intro R h
  unfold models satisfies_all at *
  intro c hc
  apply h
  simp [Finset.mem_sdiff] at hc
  exact hc.1


/--
   The set of realizations satisfying S is closed under the addition of constraints that are already satisfied by those realizations.
-/
theorem closure_under_constraint_addition (S : ConstraintSet) (C : Constraint) (R : Realization) :
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

-- TODO!

theorem unsat_models_empty (S : ConstraintSet) :
   ¬ satisfiable S ↔ models S = ∅ := sorry
  -- constructor
  -- -- · intro h
  -- --   ext R
  -- -- · simp [models, satisfiable] at *
  --   sorry


-- TODO: Empty constraint set admits all layouts

--



end Semantics

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Tactic
import CndSemantics.Definitions
import CndSemantics.Semantics

namespace Typing

open CnD
open Semantics
/--
Typing judgment: `Γ ⊢ R` means that realization `R` has type `Γ`.
This is defined as `R` satisfying all constraints in `Γ`.
-/
def well_typed (Γ : ConstraintSet) (R : Realization) : Prop :=
  ∀ C ∈ Γ, satisfies R C

/--
Typing rule: (T-Empty)
An empty constraint set always has a well-typed realization.
-/
theorem T_Empty (R : Realization) : well_typed ∅ R := by
  intro C h
  exact False.elim (Finset.notMem_empty C h)

/--
Typing rule: (T-Add)
If `Γ ⊢ R` and `R ⊨ C`, then `Γ ∪ {C} ⊢ R`.
-/
theorem T_Add (Γ : ConstraintSet) (C : Constraint) (R : Realization) :
  well_typed Γ R → satisfies R C → well_typed (Γ ∪ {C}) R := by
  intro hΓ hC
  intro C' hC'
  cases Finset.mem_union.mp hC' with
  | inl hΓ' => exact hΓ _ hΓ'
  | inr hC'' =>
    have : C' = C := by simpa using hC''
    rw [this]
    exact hC

/--
Meta-theorem: Progress
If `Γ` is satisfiable, then there exists some well-typed realization.
-/
theorem progress (Γ : ConstraintSet) :
  satisfiable Γ → ∃ R : Realization, well_typed Γ R := by
  intro h
  exact h

/--
Preservation
If `Γ ⊢ R` and `Γ ⟶ Γ ∪ {C}`, then `Γ ∪ {C} ⊢ R`.
-/
theorem preservation (Γ : ConstraintSet) (C : Constraint) (R : Realization) :
  well_typed Γ R → satisfies R C → well_typed (Γ ∪ {C}) R := by
  exact T_Add Γ C R

/--
Soundness: If `Γ ⊢ R`, then `R ∈ ⟦Γ⟧`.
This ensures that well-typed realizations are valid models.
-/
theorem soundness (Γ : ConstraintSet) (R : Realization) :
  well_typed Γ R → R ∈ models Γ := by
  intro h
  unfold models satisfies_all
  exact h


-- And now, completeness?


end Typing

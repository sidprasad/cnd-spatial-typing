import CndSemantics.Definitions

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Real.Basic

namespace CnD


-- TODO: NO overlapping boxes in a Realization.



def satisfies (R : Realization) : Constraint → Prop :=
| Constraint.left a b => atom_left_of (R a) (R b)
| Constraint.above a b => atom_above (R a) (R b)
| Constraint.horizontally_aligned a b => atom_horizontally_aligned (R a) (R b)
| Constraint.vertically_aligned a b => atom_vertically_aligned (R a) (R b)
| Constraint.group S => grouped (S.map R) R

def well_typed (Γ : Finset Constraint) (R : Realization) : Prop :=
  ∀ C ∈ Γ, satisfies R C

abbrev ConstraintSet := Finset Constraint
def satisfies_all (R : Realization) (S : ConstraintSet) : Prop :=
  ∀ c ∈ S, satisfies R c

def models (S : ConstraintSet) : Set Realization :=
  { R | satisfies_all R S }


theorem refinement (S : Finset Constraint) (C : Constraint) :
  models (S ∪ ({C} : Finset Constraint)) ⊆ models S := by
  intro R h
  unfold models satisfies_all at *
  simp at *
  exact And.left h

end CnD

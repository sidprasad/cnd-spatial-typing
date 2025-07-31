import CndSemantics.Semantics
import CndSemantics.ProofSystem

namespace CnD

-- This seems, unlikely?

theorem completeness {R : Realization} {C : Constraint} :
  satisfies R C → Provable R C := by
  intro h
  cases C with
  | left a b =>
      -- Use the definition of `satisfies` for `Constraint.left`
      -- Construct a proof using `Provable.left_rule`
      sorry
  | right a b =>
      -- Similar for `Constraint.right`
      sorry
  | above a b =>
      sorry
  | below a b =>
      sorry
  | directly_left a b =>
      sorry
  | directly_right a b =>
      sorry
  | directly_above a b =>
      sorry
  | directly_below a b =>
      sorry
  | group S =>
      -- Handle the `group_rule` case
      sorry


theorem completeness_well_typed {Γ : List Constraint} {R : Realization} :
  well_typed Γ R → (∀ C ∈ Γ, Provable R C) := by
  intro h
  intro C hC
  apply completeness
  exact h C hC

end CnD

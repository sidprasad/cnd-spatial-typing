import CndSemantics.Semantics
import CndSemantics.ProofSystem

namespace CnD

theorem soundness {R : Realization} {C : Constraint} :
  Provable R C → satisfies R C := by
  intro h
  cases h with
  | left_rule h => simp [satisfies]; exact h
  | right_rule h => simp [satisfies]; exact h
  | above_rule h => simp [satisfies]; exact h
  | below_rule h => simp [satisfies]; exact h
  | directly_left_rule h => simp [satisfies]; exact h
  | directly_right_rule h => simp [satisfies]; exact h
  | directly_above_rule h => simp [satisfies]; exact h
  | directly_below_rule h => simp [satisfies]; exact h
  | group_rule h => simp [satisfies]; exact h;

-- "Every spatially well-typed (Cope and Drag-typed) data structure can be correctly realized by a valid layout."
theorem soundness_well_typed {Γ : List Constraint} {R : Realization} :
  (∀ C ∈ Γ, Provable R C) → well_typed Γ R := by
  intro h
  unfold well_typed
  intro C hC
  apply soundness
  exact h C hC



end CnD

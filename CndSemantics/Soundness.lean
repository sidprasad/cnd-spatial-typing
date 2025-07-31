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
  | group_rule => simp [satisfies]

end CnD

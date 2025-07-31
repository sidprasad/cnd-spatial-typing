import CndSemantics.Semantics
import CndSemantics.ProofSystem
import CnDSemantics.Soundness

namespace CnD

-- Consistency here means
-- "Constraint sets without realizations never admit well-typed instances."

theorem consistency {Γ : List Constraint} :
  (¬ ∃ R, well_typed Γ R) → ∀ R, ¬ well_typed Γ R := by
  intro h;

  sorry



end CnD

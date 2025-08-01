import CndSemantics.Semantics
import CndSemantics.ProofSystem
import CndSemantics.Soundness

namespace CnD

-- Definition: A constraint set is satisfiable if there exists a
-- realization that satisfies all constraints
def Satisfiable (Γ : List Constraint) : Prop :=
  ∃ R : Realization, well_typed Γ R

-- Definition: A constraint set is unsatisfiable if no realization can satisfy all constraints
def Unsatisfiable (Γ : List Constraint) : Prop :=
  ¬ Satisfiable Γ


-- Some assumptions:
-- Finite number of boxes
-- Finite number of constraints


-- We already have a satisfies function that checks if a realization satisfies a constraint.

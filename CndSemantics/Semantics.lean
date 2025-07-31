import CndSemantics.Boxes
import CndSemantics.Constraints

namespace CnD

def satisfies (R : Realization) : Constraint → Prop
| Constraint.left a b => left_of (R a) (R b)
| Constraint.right a b => right_of (R a) (R b)
| Constraint.above a b => above (R a) (R b)
| Constraint.below a b => below (R a) (R b)
| Constraint.directly_left a b => directly_left (R a) (R b)
| Constraint.directly_right a b => directly_right (R a) (R b)
| Constraint.directly_above a b => directly_above (R a) (R b)
| Constraint.directly_below a b => directly_below (R a) (R b)
| Constraint.group S => True  -- For now, group constraints are always satisfied

def well_typed (Γ : List Constraint) (R : Realization) : Prop :=
  ∀ C ∈ Γ, satisfies R C

end CnD

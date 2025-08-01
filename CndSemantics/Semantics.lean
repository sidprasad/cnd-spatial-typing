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
| Constraint.group S => grouped (S.map R) R

def well_typed (Γ : List Constraint) (R : Realization) : Prop :=
  ∀ C ∈ Γ, satisfies R C


def decidable_satisfies (R : Realization) (C : Constraint) : Decidable (satisfies R C) :=
  match C with
  | Constraint.left a b =>
    if h : left_of (R a) (R b) then isTrue h else isFalse h
  | Constraint.right a b =>
    if h : right_of (R a) (R b) then isTrue h else isFalse h
  | Constraint.above a b =>
    if h : above (R a) (R b) then isTrue h else isFalse h
  | Constraint.below a b =>
    if h : below (R a) (R b) then isTrue h else isFalse h
  | Constraint.directly_left a b =>
    if h : directly_left (R a) (R b) then isTrue h else isFalse h
  | Constraint.directly_right a b =>
    if h : directly_right (R a) (R b) then isTrue h else isFalse h
  | Constraint.directly_above a b =>
    if h : directly_above (R a) (R b) then isTrue h else isFalse h
  | Constraint.directly_below a b =>
    if h : directly_below (R a) (R b) then isTrue h else isFalse h
  | Constraint.group S =>
    if h : grouped (S.map R) R then isTrue h else isFalse h
end CnD

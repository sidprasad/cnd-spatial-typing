import CndSemantics.Boxes
import CndSemantics.Constraints

namespace CnD

inductive Provable : Realization → Constraint → Prop
| left_rule {R : Realization} {a b : Nat}
    (h : left_of (R a) (R b)) :
    Provable R (Constraint.left a b)
| right_rule {R : Realization} {a b : Nat}
    (h : right_of (R a) (R b)) :
    Provable R (Constraint.right a b)
| above_rule {R : Realization} {a b : Nat}
    (h : above (R a) (R b)) :
    Provable R (Constraint.above a b)
| below_rule {R : Realization} {a b : Nat}
    (h : below (R a) (R b)) :
    Provable R (Constraint.below a b)
| directly_left_rule {R : Realization} {a b : Nat}
    (h : directly_left (R a) (R b)) :
    Provable R (Constraint.directly_left a b)
| directly_right_rule {R : Realization} {a b : Nat}
    (h : directly_right (R a) (R b)) :
    Provable R (Constraint.directly_right a b)
| directly_above_rule {R : Realization} {a b : Nat}
    (h : directly_above (R a) (R b)) :
    Provable R (Constraint.directly_above a b)
| directly_below_rule {R : Realization} {a b : Nat}
    (h : directly_below (R a) (R b)) :
    Provable R (Constraint.directly_below a b)
| group_rule {R : Realization} {S : List Nat} :
    Provable R (Constraint.group S)

end CnD

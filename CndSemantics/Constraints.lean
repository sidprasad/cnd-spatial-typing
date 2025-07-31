namespace CnD

inductive Constraint
| left           (a b : Nat)
| right          (a b : Nat)
| above          (a b : Nat)
| below          (a b : Nat)
| directly_left  (a b : Nat)
| directly_right (a b : Nat)
| directly_above (a b : Nat)
| directly_below (a b : Nat)
| group          (S : List Nat)
deriving Repr, BEq

end CnD

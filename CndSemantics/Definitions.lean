import Mathlib.Data.Finset.Basic
import Mathlib.Data.Real.Basic
import Std.Data.HashMap


namespace CnD

structure Rect where
  xmin : Rat
  ymin : Rat
  xmax : Rat
  ymax : Rat


structure Box where
  xmin : Rat
  ymin : Rat
  width : Rat
  height : Rat
deriving BEq



instance : Inhabited Box where
  default := { xmin := 0.0, ymin := 0.0, width := 1.0, height := 1.0 }

abbrev Atom := Nat
abbrev Realization := Atom → Option Box



def horizontally_aligned (a b : Box) : Bool := a.ymin = b.ymin
def vertically_aligned (a b : Box) : Bool := a.xmin  = b.xmin

def left_of (a b : Box) : Bool := a.xmin + a.width < b.xmin
-- def right_of (a b : Box) : Bool := a.xmin + a.width > b.xmin
def above (a b : Box) : Bool := a.ymin + a.height < b.ymin
-- def below (a b : Box) : Bool := (a.ymin + a.height) > b.ymin

-- def directly_left (a b : Box) : Bool := a.xmin + a.width = b.xmin ∧ horizontally_aligned a b
-- def directly_right (a b : Box) : Bool := b.xmin + b.width = a.xmin ∧ horizontally_aligned a b
-- def directly_above (a b : Box) : Bool := a.ymin + a.height = b.ymin ∧ vertically_aligned a b
-- def directly_below (a b : Box) : Bool := b.ymin + b.height = a.ymin ∧ vertically_aligned a b



-- TODO: Cyclic constraints.





-- NOW WE NEED TO WRITE THE ATOM VERSION OF THESE FUNCTIONS (IS THIS OVERKILL?)
def atom_left_of (a b : Atom) (realization : Realization) : Bool :=
  match realization a, realization b with
  | some boxA, some boxB => left_of boxA boxB
  | _, _ => false


def atom_above (a b : Atom) (realization : Realization) : Bool :=
  match realization a, realization b with
  | some boxA, some boxB => above boxA boxB
  | _, _ => false


def atom_horizontally_aligned (a b : Atom) (realization : Realization) : Bool :=
  match realization a, realization b with
  | some boxA, some boxB => horizontally_aligned boxA boxB
  | _, _ => false

def atom_vertically_aligned (a b : Atom) (realization : Realization) : Bool :=
  match realization a, realization b with
  | some boxA, some boxB => vertically_aligned boxA boxB
  | _, _ => false




def contains (rect : Rect) (box : Box) : Bool :=
  rect.xmin ≤ box.xmin &&
  box.xmin + box.width ≤ rect.xmax &&
  rect.ymin ≤ box.ymin &&
  box.ymin + box.height ≤ rect.ymax

-- I think we need to re write this.
-- I think it is wrong?
def grouped (boxes : List Box) (realization : Realization) : Prop :=
  ∃ (rect : Rect),
    -- Every box in the list is contained in the rectangle
    (∀ box ∈ boxes, contains rect box) ∧
    -- No box not in the list is contained in the rectangle
    (∀ (n : Atom), match realization n with
                   | some box => contains rect box → ∃ b ∈ boxes, b = box
                   | none => True)



def atoms_grouped (atoms : List Atom) (realization : Realization) : Prop :=
  ∃ (rect : Rect),
    -- Every box corresponding to the atoms is contained in the rectangle
    (∀ atom ∈ atoms, match realization atom with
                     | some box => contains rect box
                     | none => False)
      ∧
    -- No box not corresponding to the atoms is contained in the rectangle
    (∀ (n : Atom), match realization n with
                   | some box => contains rect box → n ∈ atoms
                   | none => True)



-- Reduce this to the key (non-sugared constraints)
inductive Constraint
| left           (a b : Atom)
| above          (a b : Atom)
| horizontally_aligned (a b : Atom)
| vertically_aligned (a b : Atom)
| group          (S : Finset Atom) -- Maybe this should be finset?

deriving BEq, DecidableEq

def satisfies (R : Realization) : Constraint → Prop
| Constraint.left a b => atom_left_of a b R
| Constraint.above a b => atom_above a b R
| Constraint.horizontally_aligned a b => atom_horizontally_aligned a b R
| Constraint.vertically_aligned a b => atom_vertically_aligned a b R
| Constraint.group S => atoms_grouped (S.toList) R




end CnD

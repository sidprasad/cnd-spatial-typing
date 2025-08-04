import Mathlib.Data.Finset.Basic
import Mathlib.Data.Real.Basic


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
def above (a b : Box) : Bool := a.ymin + a.height < b.ymin


-- TODO: Cyclic constraints.
-- All cyclic constraints compile to a combination of the basic constraints.


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
| group          (S : Finset Atom)

deriving BEq, DecidableEq

def satisfies (R : Realization) : Constraint → Prop
| Constraint.left a b => atom_left_of a b R
| Constraint.above a b => atom_above a b R
| Constraint.horizontally_aligned a b => atom_horizontally_aligned a b R
| Constraint.vertically_aligned a b => atom_vertically_aligned a b R
| Constraint.group S => atoms_grouped (S.toList) R


def overlap (a b : Box) : Bool :=
  let horizontal_overlap := a.xmin < b.xmin + b.width ∧ b.xmin < a.xmin + a.width
  let vertical_overlap := a.ymin < b.ymin + b.height ∧ b.ymin < a.ymin + a.height
  horizontal_overlap ∧ vertical_overlap

def well_formed (R : Realization) : Prop :=
  ∀ a, match R a with
       | some box => box.height > 0 ∧ box.width > 0
       | none => True
  ∧
  ∀ a b, a ≠ b → match R a, R b with
                 | some boxA, some boxB =>
                     ¬ overlap boxA boxB
                 | _, _ => True
  -- What about how each atom is assigned to at most one box?
  ∧
  ∀ a b, a ≠ b → match R a, R b with
                 | some boxA, some boxB => boxA ≠ boxB
                 | _, _ => True




end CnD

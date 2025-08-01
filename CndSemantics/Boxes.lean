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
-- Finiteness is important.
abbrev Realization := List (Atom × Box)

def box_for_atom (realization : Realization) (atom : Atom) : Option Box :=
  realization.find? (fun pair => pair.1 = atom) |>.map (fun pair => pair.2)


def horizontally_aligned (a b : Box) : Bool := a.ymin = b.ymin

def vertically_aligned (a b : Box) : Bool := a.xmin  = b.xmin

def left_of (a b : Box) : Bool := a.xmin + a.width < b.xmin
def right_of (a b : Box) : Bool := a.xmin + a.width > b.xmin
def above (a b : Box) : Bool := a.ymin + a.height < b.ymin
def below (a b : Box) : Bool := (a.ymin + a.height) > b.ymin

def directly_left (a b : Box) : Bool := a.xmin + a.width = b.xmin ∧ horizontally_aligned a b
def directly_right (a b : Box) : Bool := b.xmin + b.width = a.xmin ∧ horizontally_aligned a b
def directly_above (a b : Box) : Bool := a.ymin + a.height = b.ymin ∧ vertically_aligned a b
def directly_below (a b : Box) : Bool := b.ymin + b.height = a.ymin ∧ vertically_aligned a b




def contains (rect : Rect) (box : Box) : Bool :=
  rect.xmin ≤ box.xmin &&
  box.xmin + box.width ≤ rect.xmax &&
  rect.ymin ≤ box.ymin &&
  box.ymin + box.height ≤ rect.ymax


-- TODO: The types need to line up now.

def grouped (boxes : List Box) (realization : Realization) : Prop :=
  ∃ (rect : Rect),
    -- Every box in the list is contained in the rectangle
    (∀ box ∈ boxes, contains rect box) ∧
    -- No box not in the list is contained in the rectangle
    (∀ (n : Atom), match box_for_atom realization n with
                   | some box => contains rect box → ∃ b ∈ boxes, b = box
                   | none => True)

def grouped_bool (boxes : List Box) (realization : Realization) : Bool :=
  ∃ rect : Rect,
    -- Every box in the list is contained in the rectangle
    boxes.all (fun box => contains rect box) &&
    -- No box not in the list is contained in the rectangle
    realization.all (fun (atom_box : Atom × Option Box) =>
      match atom_box.snd with
      | some box => contains rect box → boxes.any (fun b => b == box)
      | none => true)


end CnD

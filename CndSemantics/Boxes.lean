namespace CnD

structure Box where
  xmin : Float
  ymin : Float
  width : Float
  height : Float
deriving Repr

instance : Inhabited Box where
  default := { xmin := 0.0, ymin := 0.0, width := 1.0, height := 1.0 }

abbrev Realization := Nat → Box

def horizontally_aligned (a b : Box) : Prop := a.ymin = b.ymin

def vertically_aligned (a b : Box) : Prop := a.xmin  = b.xmin

def left_of (a b : Box) : Prop := a.xmin + a.width < b.xmin
def right_of (a b : Box) : Prop := a.xmin + a.width > b.xmin
def above (a b : Box) : Prop := a.ymin + a.height < b.ymin
def below (a b : Box) : Prop := a.ymin + a.height > b.ymin

def directly_left (a b : Box) : Prop := a.xmin + a.width = b.xmin ∧ horizontally_aligned a b
def directly_right (a b : Box) : Prop := b.xmin + b.width = a.xmin ∧ horizontally_aligned a b
def directly_above (a b : Box) : Prop := a.ymin + a.height = b.ymin ∧ vertically_aligned a b
def directly_below (a b : Box) : Prop := b.ymin + b.height = a.ymin ∧ vertically_aligned a b



end CnD

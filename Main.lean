/-
# CnD: A Spatial Semantics

This literate Lean file presents Cope and Drag (CnD) constraints
as a **spatial semantics**:

* A program is a finite set of spatial constraints.
* Its denotation is the set of realizations (layouts) that satisfy those constraints.
* A solver implements the operational semantics: picking one realization or failing.
-/

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Data.List.Basic
import Mathlib.Tactic


namespace CnD

--------------------------------------------------------------------------------
-- §1 Atoms, Boxes, Realizations
--------------------------------------------------------------------------------

/--
Atoms are the basic diagram elements. Each atom has an identifier and dimensions (which identify its footprint).
-/
structure Atom where
  id     : Nat
  width  : Rat
  height : Rat
deriving BEq, DecidableEq

instance : Inhabited Atom where
  default := { id := 0, width := 1, height := 1 }


/--
A box is a placed footprint of an atom on the canvas.
-/
structure Box where
  xmin   : Rat
  ymin   : Rat
  width  : Rat
  height : Rat
deriving BEq, DecidableEq

-- We define some spatial primitives for boxes in terms of coordinate systems.
def horizontally_aligned (a b : Box) : Prop := a.ymin = b.ymin
def vertically_aligned   (a b : Box) : Prop := a.xmin = b.xmin
def left_of              (a b : Box) : Prop := a.xmin + a.width < b.xmin
def above                (a b : Box) : Prop := a.ymin + a.height < b.ymin


-- Rectangular region to define group boundaries
structure GroupBoundary where
  xmin : Rat
  ymin : Rat
  xmax : Rat
  ymax : Rat

def contains (rect : GroupBoundary) (box : Box) : Prop :=
  rect.xmin ≤ box.xmin ∧
  box.xmin + box.width ≤ rect.xmax ∧
  rect.ymin ≤ box.ymin ∧
  box.ymin + box.height ≤ rect.ymax


--- And some utilities for cyclic geometry ---

/-- Angle step between atoms on a circle of size `n`. -/
noncomputable def angleStep (n : Nat) : ℝ := (2 * Real.pi) / n



--------------------------------------------------------------------------------
-- §2 Well-formed Realizations
--------------------------------------------------------------------------------


/--
A realization is an assignment of boxes to atoms.
-/
abbrev Realization := Atom → Box

def overlap (a b : Box) : Prop :=
  let horiz := a.xmin < b.xmin + b.width ∧ b.xmin < a.xmin + a.width
  let vert  := a.ymin < b.ymin + b.height ∧ b.ymin < a.ymin + a.height
  horiz ∧ vert


/--
A realization is well-formed if:
* each box has positive dimensions,
* distinct atoms do not overlap,
* and distinct atoms map to distinct boxes.
-/
def well_formed (R : Realization) : Prop :=
  (∀ a, (R a).height > 0 ∧ (R a).width > 0)
  ∧
  (∀ a b, a ≠ b → ¬ overlap (R a) (R b))
  ∧
  (∀ a b, a ≠ b → (R a) ≠ (R b))


/--
The universe of realizations we care about: those that are well-formed.
-/
def WF : Set Realization := { R | well_formed R }


--------------------------------------------------------------------------------
-- §3 Constraints and Programs
--------------------------------------------------------------------------------

/--
Orientation constraints describe primitive geometric relations
between pairs of atoms.
-/
inductive OrientationConstraint
| left (a b : Atom)
| directly_left (a b : Atom)
| above (a b : Atom)
| directly_above (a b : Atom)
| vertically_aligned (a b : Atom)
| horizontally_aligned (a b : Atom)

deriving BEq, DecidableEq
-- Lift to atoms


def atom_horizontally_aligned (a b : Atom) (R : Realization) : Prop :=
  well_formed R ∧ horizontally_aligned (R a) (R b)

def atom_vertically_aligned (a b : Atom) (R : Realization) : Prop :=
  well_formed R ∧ vertically_aligned (R a) (R b)

def atom_left_of (a b : Atom) (R : Realization) : Prop :=
  well_formed R ∧ left_of (R a) (R b)

def atom_above (a b : Atom) (R : Realization) : Prop :=
  well_formed R ∧ above (R a) (R b)

-- Orientation satisfaction
def satisfies_orient (R : Realization) : OrientationConstraint → Prop
| .left a b                 => atom_left_of a b R
| .above a b                => atom_above a b R
| .directly_left a b        => atom_left_of a b R ∧ atom_horizontally_aligned a b R
| .directly_above a b       => atom_above a b R ∧ atom_vertically_aligned a b R
| .vertically_aligned a b    => atom_vertically_aligned a b R
| .horizontally_aligned a b  => atom_horizontally_aligned a b R



/--
The full constraint language has three forms:
1. Orientation constraints,
2. Grouping constraints,
3. Cyclic constraints.
-/
inductive Constraint
| orient (c : OrientationConstraint)
| group  (S : Finset Atom)
| cyclic (L : List Atom)
deriving BEq, DecidableEq


def atoms_grouped (S : Finset Atom) (R : Realization) : Prop :=
  ∃ rect : GroupBoundary,
    (∀ a ∈ S, contains rect (R a)) ∧
    (∀ a, contains rect (R a) → a ∈ S)




/--
Generate orientation constraints from the relative angular placement of two atoms.
We place atoms on the unit circle, compute their cosine/sine coordinates,
and derive left/above/alignment constraints from comparisons.
  -/
  noncomputable def constraints_from_angles (a b : Atom) (θa θb : ℝ) : Finset OrientationConstraint :=
    let xa := Real.cos θa
    let ya := Real.sin θa
    let xb := Real.cos θb
    let yb := Real.sin θb
    ∅
    -- horizontal relation
    |> (if xa < xb then (· ∪ {OrientationConstraint.left a b})
        else if xa > xb then (· ∪ {OrientationConstraint.left b a})
        else (· ∪ {OrientationConstraint.vertically_aligned a b}))
    -- vertical relation
    |> (if ya < yb then (· ∪ {OrientationConstraint.above a b})
        else if ya > yb then (· ∪ {OrientationConstraint.above b a})
        else (· ∪ {OrientationConstraint.horizontally_aligned a b}))

  /--
  Constraints for perturbation `k` of a cycle of atoms.
  Atoms are arranged evenly on the unit circle,
  rotated by offset `k`.
  -/
  noncomputable def perturbation_constraints (L : List Atom) (k : Nat) : Finset OrientationConstraint :=
    let n := L.length
    let step := angleStep n
    let angles := (List.range n).map (fun i => (i + k) * step)
    (List.range n).foldl (fun acc i =>
      let a := L[i]!
      let b := L[(i+1) % n]!  -- wrap-around
      acc ∪ constraints_from_angles a b (angles[i]!) (angles[(i+1) % n]!)) ∅

/--
A realization satisfies a cyclic constraint at perturbation `k`
if it satisfies all orientation constraints generated by that perturbation.
-/
noncomputable def satisfies_perturbation (R : Realization) (L : List Atom) (k : Nat) : Prop :=
  ∀ C ∈ perturbation_constraints L k, satisfies_orient R C

--------------------------------------------------------------------------------
-- §4 Semantics
--------------------------------------------------------------------------------


abbrev Program := Finset Constraint

def satisfies_constraint (R : Realization) : Constraint → Prop
| .orient c => satisfies_orient R c
| .group S  => atoms_grouped S R
| .cyclic L => ∃ k < L.length, satisfies_perturbation R L k


def satisfies_program (R : Realization) (P : Program) : Prop :=
  ∀ C ∈ P, satisfies_constraint R C


--------------------------------------------------------------------------------
-- §5 Denotational Semantics
--------------------------------------------------------------------------------

/--
The denotation of a *program* is the set of realizations
that satisfy all constraints in the program,
and are well-formed.
-/
def denotes (P : Finset Constraint) : Set Realization :=
  { R | R ∈ WF ∧ satisfies_program R P }

notation "⟦" P "⟧" => denotes P


lemma denotes_empty : ⟦∅⟧ = WF := by
  simp [denotes, satisfies_program]



--------------------------------------------------------------------------------
-- §6 Key Meta Theorems
--------------------------------------------------------------------------------

/--
Adding a constraint refines the denotation (shrinks the set).
-/
theorem refinement (P : Program) (C : Constraint) :
  denotes (P ∪ {C}) ⊆ ⟦P⟧ := by
  intro R h
  simp [denotes, satisfies_program] at *
  rcases h with ⟨hWF, hSat⟩
  constructor
  · exact hWF
  · intro D hD
    apply hSat
    simp [hD]

/--
Corollary to `refinement`. If a program `P` is a subset of `Q`,
then the denotation of `Q` is a superset of the denotation of `P`.
-/
theorem monotonicity {P Q : Program} (hPQ : P ⊆ Q) : (denotes Q) ⊆ (denotes P) := by
  intro R hR
  simp [denotes, satisfies_program] at *
  rcases hR with ⟨hWF, hSatQ⟩
  refine ⟨hWF, ?_⟩
  intro D hDP
  exact hSatQ D (hPQ hDP)

--------------------------------------------------------------------------------
-- §7 Syntactic Sugar
--------------------------------------------------------------------------------

namespace Sugar

/--
Syntactic sugar for `right_of`: `a` is to the right of `b`.
-/
def atom_right_of (a b : Atom) : Constraint :=
  Constraint.orient (OrientationConstraint.left b a)

/--
Syntactic sugar for `below`: `a` is below `b`.
-/
def atom_below (a b : Atom) : Constraint :=
  Constraint.orient (OrientationConstraint.above b a)


/--
Syntactic sugar for `directly_right`: `a` is directly to the right of `b`.
-/
def atom_directly_right (a b : Atom) : Constraint :=
Constraint.orient (OrientationConstraint.directly_left b a)



/--
Syntactic sugar for `directly_below`: `a` is directly below `b`.
-/
def atom_directly_below (a b : Atom) : Constraint :=
  Constraint.orient (OrientationConstraint.directly_above b a)


/--
Syntactic sugar for `cyclic_counterclockwise`: reverse the list of atoms
and apply the cyclic constraint.
-/
def cyclic_counterclockwise (L : List Atom) : Constraint :=
  Constraint.cyclic L.reverse

end Sugar



end CnD

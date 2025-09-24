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

import Std.Data.HashMap


namespace CnD

--------------------------------------------------------------------------------
-- §1 Atoms, Boxes, Realizations
--------------------------------------------------------------------------------

/--
Atoms are the basic PROGRAM elements. Each atom has an identifier.
-/
structure Atom where
  id     : Nat
  -- width  : Rat
  -- height : Rat
deriving BEq, DecidableEq

/-- Needed later for cyclic constr. -/
instance : Hashable Atom where
  hash a := hash a.id

instance : Inhabited Atom where
  default := { id := 0}


/--
Boxes are realizations of atoms in 2D space.
They exist at the layout/diagram level.
-/
structure Box where
  xmin   : Rat
  ymin   : Rat
  width  : Rat
  height : Rat
deriving BEq, DecidableEq

/-
These are the predicates
that operate on boxes.
-/
def horizontally_aligned (a b : Box) : Prop := a.ymin = b.ymin
def vertically_aligned   (a b : Box) : Prop := a.xmin = b.xmin
def left_of              (a b : Box) : Prop := a.xmin + a.width < b.xmin
def above                (a b : Box) : Prop := a.ymin + a.height < b.ymin


/--

  Group boundaries are ANOTHER layout/diagram-level construct.
-/
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

/-- Angle step between `n` atoms on a circle. -/
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

/--
A program is just a finite set of constraints.
-/
abbrev Program := Finset Constraint

/-- Programs compose by union -/
def Program.compose (P Q : Program) : Program :=
  P ∪ Q

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



--------------------------------------------------------------------------------
-- §8 Selectors
--------------------------------------------------------------------------------

-- But CnD specs are written in terms of selectors,
-- which are a set of atoms that are selected by the user.

-- There are two kinds of selectors:
-- 1. Arity-1 selectors: Sets of atoms, e.g. `{ A, B }`
-- 2. Arity-2 selectors: Pairs of atoms, e.g. `{ (A, B), (B, C) }`

/--
An arity-1 selector: a set of atoms.
-/
abbrev Selector1 := Finset Atom

/--
An arity-2 selector: a set of pairs of atoms.
-/
abbrev Selector2 := Finset (Atom × Atom)

-- Orientation Constraints take Arity-2 selectors and apply them to each pair of atoms.
/--
Apply an orientation constraint to all pairs in an arity-2 selector.
-/
def apply_orientation (sel : Selector2) (c : Atom → Atom → OrientationConstraint) : Program :=
  sel.image (fun (a, b) => Constraint.orient (c a b))

-- Group Constraints take Arity-1 selectors and apply them to the set of atoms.
/--
Apply a grouping constraint to all atoms in an arity-1 selector.
-/
def apply_grouping (sel : Selector1) : Program :=
  { Constraint.group sel }

/--
Build groups from arity-2 selector pairs.
The first element of each pair is the "key" and the second element joins that key's group.
The key itself is NOT included in the group.
e.g. { (A, B), (A, C), (D, E) } -> { {B, C}, {E} }
-/
noncomputable def build_groups (sel : Selector2) : Finset (Finset Atom) :=
  -- Build a map from key atoms to their associated atoms (excluding the key)
  let groupMap : Std.HashMap Atom (Finset Atom) :=
    sel.toList.foldl (fun (acc : Std.HashMap Atom (Finset Atom)) (pair : Atom × Atom) =>
      let (key, value) := pair
      let existing := acc.getD key ∅  -- Start with empty set (key not included)
      acc.insert key (existing ∪ {value})  -- Use union with singleton set
    ) {}

  -- Convert the map values to a finset of groups
  groupMap.fold (fun (acc : Finset (Finset Atom)) (_ : Atom) (atomSet : Finset Atom) =>
    acc ∪ {atomSet}) ∅

/--
Apply grouping constraints for arity-2 selectors.
Groups atoms where the first element is the key, but the key is not in the group.
e.g. { (A, B), (A, C), (D, E) } -> { {B, C}, {E} }
-/
noncomputable def apply_grouping_arity2 (sel : Selector2) : Program :=
  let groups := build_groups sel
  groups.image (fun s => Constraint.group s)

--------------------------------------------------------------------------------
-- §8.1 Cyclic Constraints

-- Cyclic Constraints take Arity-2 selectors interpreting them as adjacency pairs.
-- { (A, B) , (B, C), (C, A) }  --> [A, B, C]
-- { (A, B), (C, D), (B, C) }  --> [A, B, C, D]
-- { (A, B), (A, C) } -> { [A, B], [A, C] }
--------------------------------------------------------------------------------

-- Helpers --
/--
Build a mapping from each atom to its list of successors based on the input pairs.
-/
def build_next_atom_map (pairs : List (Atom × Atom)) : Atom → List Atom :=
  let adjacency : Std.HashMap Atom (List Atom) :=
    pairs.foldl (fun acc (a, b) =>
      let curr := acc.getD a []
      acc.insert a (b :: curr)) ∅
  fun atom => adjacency.getD atom []

/--
Traverse the graph from a given atom, enumerating all paths.
Stop traversal if an atom is revisited.
-/
def traverse_paths (start : Atom) (nextAtomMap : Atom → List Atom) (allAtoms : Finset Atom) : List (List Atom) :=
  let rec dfs (current : Atom) (visited : List Atom) (remaining : Nat) : List (List Atom) :=
    if remaining = 0 then [visited.reverse]  -- Safety bound
    else if visited.contains current then [visited.reverse]  -- Cycle detected
    else
      let neighbors := nextAtomMap current
      neighbors.flatMap (fun neighbor => dfs neighbor (current :: visited) (remaining - 1))
  -- We're leveraging the fact that we have a finite set of atoms to limit
  -- the depth of our search.
  dfs start [] allAtoms.card

/--
Check if two paths are equivalent under rotation.
-/
def paths_equivalent (path1 path2 : List Atom) : Bool :=
  path1.length = path2.length &&
  (List.range path1.length).any (fun i => path1.rotateLeft i = path2)

/--
Check if one path is a subpath of another, considering rotations.
For cyclic paths, we need to check if the shorter path appears as
a contiguous subsequence in any rotation of the longer path.
-/
def is_cyclic_subpath (sub : List Atom) (super : List Atom) : Bool :=
  if sub.length >= super.length then false
  else
    -- Check if sub appears as a contiguous subsequence in any rotation of super
    (List.range super.length).any (fun i =>
      let rotated := super.rotateLeft i
      rotated.take sub.length = sub)

/--
Remove equivalent paths and subpaths while preserving order.
This function:
1. Removes rotational duplicates (keeping the first occurrence)
2. Removes paths that are cyclic subpaths of other paths
-/
def deduplicate_and_filter_cyclic_subpaths (paths : List (List Atom)) : List (List Atom) :=
  -- Step 1: Remove rotational duplicates
  let deduplicated := paths.foldl (fun acc path =>
    if acc.any (fun existing => paths_equivalent existing path)
    then acc
    else acc ++ [path]
  ) []

  -- Step 2: Remove cyclic subpaths
  deduplicated.filter (fun path =>
    ¬ deduplicated.any (fun other => is_cyclic_subpath path other))

/--
Convert a `List (Atom × Atom)` into a `List (List Atom)`, where each inner list
represents a unique cycle derived from the input pairs.
-/
noncomputable def pairs_to_unique_cycles (pairs : List (Atom × Atom)) : List (List Atom) :=
  let nextAtomMap := build_next_atom_map pairs
  -- Get all unique starting atoms
  let startAtoms := (pairs.map Prod.fst ++ pairs.map Prod.snd).toFinset
  let allPaths := startAtoms.toList.flatMap (fun start => traverse_paths start nextAtomMap startAtoms)
  deduplicate_and_filter_cyclic_subpaths allPaths

/--
Build a cyclic constraint from an arity-2 selector.
-/
noncomputable def apply_cyclic (sel : Selector2) : Program :=
  let cycles := pairs_to_unique_cycles sel.toList
  cycles.foldl (fun acc cycle => acc ∪ {Constraint.cyclic cycle}) ∅

-- Surface constraints are what
-- users specify in CnD specs.
inductive CnDConstraint
| orient (sel : Selector2) (c : Atom → Atom → OrientationConstraint)
| group1  (sel : Selector1)
| group2 (sel: Selector2)
| cyclic (sel : Selector2)

/--
Convert a surface constraint to a program.
-/
noncomputable def CnDConstraint.toProgram : CnDConstraint → Program
| .orient sel c => apply_orientation sel c
| .group1 sel => apply_grouping sel
| .group2 sel => apply_grouping_arity2 sel
| .cyclic sel => apply_cyclic sel


/--
Combine all surface constraints into a program.
-/
noncomputable def surface_constraints_to_program (scs : List CnDConstraint) : Program :=
  scs.foldl (fun acc sc => Program.compose acc sc.toProgram) ∅

end CnD

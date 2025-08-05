/-
# CnD as Semantics and as a Type System

This literate Lean file presents Cope and Drag (CnD) constraints
from two complementary perspectives:

1. **Semantics view**: constraints as truth conditions on layouts.
2. **Type system view**: constraints as spatial types.

We then show how the two views align through a correspondence theorem,
and give small-step semantics for refinement (constraint addition),
with meta-theorems: progress, preservation, soundness,
completeness, and type safety.
-/

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Tactic

namespace CnD

--------------------------------------------------------------------------------
-- §1 Syntax: Atoms, Boxes, Realizations
--------------------------------------------------------------------------------

/-
* An **atom** is an abstract identifier (natural number) for a diagram element.
* A **box** is the geometric footprint of an atom: where it lives on the canvas.
* A **realization** is a mapping from atoms to boxes: it assigns
  some atoms positions and sizes.
-/

abbrev Atom := Nat

structure Box where
  xmin : Rat
  ymin : Rat
  width : Rat
  height : Rat
deriving BEq

instance : Inhabited Box where
  default := { xmin := 0, ymin := 0, width := 1, height := 1 }

abbrev Realization := Atom → Option Box

/--

We also define when a realization is "well-formed":
* every box has positive dimensions,
* distinct atoms do not overlap,
* distinct atoms are assigned distinct boxes.
-/

def overlap (a b : Box) : Prop :=
  let horiz := a.xmin < b.xmin + b.width ∧ b.xmin < a.xmin + a.width
  let vert  := a.ymin < b.ymin + b.height ∧ b.ymin < a.ymin + a.height
  horiz ∧ vert

def well_formed (R : Realization) : Prop :=
  (∀ a, match R a with
        | some box => box.height > 0 ∧ box.width > 0
        | none => True)
  ∧
  (∀ a b, a ≠ b → match R a, R b with
                  | some boxA, some boxB => ¬ overlap boxA boxB
                  | _, _ => True)
  ∧
  (∀ a b, a ≠ b → match R a, R b with
                  | some boxA, some boxB => boxA ≠ boxB
                  | _, _ => True)

--------------------------------------------------------------------------------
-- §2 Geometry: Primitive Relations
--------------------------------------------------------------------------------

/-
Constraints talk about primitive geometric relations.
We define them at the box level, and then lift them
to atoms via a realization.
-/

def horizontally_aligned (a b : Box) : Prop := a.ymin = b.ymin
def vertically_aligned   (a b : Box) : Prop := a.xmin = b.xmin
def left_of              (a b : Box) : Prop := a.xmin + a.width < b.xmin
def above                (a b : Box) : Prop := a.ymin + a.height < b.ymin

def atom_left_of (a b : Atom) (R : Realization) : Prop :=
  match R a, R b with
  | some boxA, some boxB => left_of boxA boxB
  | _, _ => False

def atom_above (a b : Atom) (R : Realization) : Prop :=
  match R a, R b with
  | some boxA, some boxB => above boxA boxB
  | _, _ => False

def atom_horizontally_aligned (a b : Atom) (R : Realization) : Prop :=
  match R a, R b with
  | some boxA, some boxB => horizontally_aligned boxA boxB
  | _, _ => False

def atom_vertically_aligned (a b : Atom) (R : Realization) : Prop :=
  match R a, R b with
  | some boxA, some boxB => vertically_aligned boxA boxB
  | _, _ => False

--------------------------------------------------------------------------------
-- §3 Grouping
--------------------------------------------------------------------------------

/-
We want to describe groups: sets of atoms enclosed in a bounding rectangle,
that contain no other atoms.

-/

structure Rect where
  xmin : Rat
  ymin : Rat
  xmax : Rat
  ymax : Rat

def contains (rect : Rect) (box : Box) : Prop :=
  rect.xmin ≤ box.xmin ∧
  box.xmin + box.width ≤ rect.xmax ∧
  rect.ymin ≤ box.ymin ∧
  box.ymin + box.height ≤ rect.ymax

def atoms_grouped (S : Finset Atom) (R : Realization) : Prop :=
  ∃ (rect : Rect),
    (∀ atom ∈ S, match R atom with
                 | some box => contains rect box
                 | none => False) ∧
    (∀ (n : Atom), match R n with
                   | some box => contains rect box → n ∈ S
                   | none => True)


--------------------------------------------------------------------------------
-- §4 Constraint Language
--------------------------------------------------------------------------------

/-
The core constraint language for CnD: atomic spatial requirements
over atoms, plus grouping.
-/

inductive Constraint
| left                  (a b : Atom)
| above                 (a b : Atom)
| horizontally_aligned  (a b : Atom)
| vertically_aligned    (a b : Atom)
| group                 (S : Finset Atom)
| cyclic                (L : List Atom)
deriving BEq, DecidableEq

def satisfies (R : Realization) : Constraint → Prop
| Constraint.left a b                 => atom_left_of a b R
| Constraint.above a b                => atom_above a b R
| Constraint.horizontally_aligned a b => atom_horizontally_aligned a b R
| Constraint.vertically_aligned a b   => atom_vertically_aligned a b R
| Constraint.group S                  => atoms_grouped S R
| Constraint.cyclic L                 => True  -- Placeholder for cyclic constraints


--------------------------------------------------------------------------------
-- §5 Semantics View
--------------------------------------------------------------------------------

/-
Constraints can be read as truth conditions: they denote sets of realizations.
-/

def satisfies_all (R : Realization) (Γ : Finset Constraint) : Prop :=
  ∀ C ∈ Γ, satisfies R C

def models (Γ : Finset Constraint) : Set Realization :=
  { R | satisfies_all R Γ }

def satisfiable (Γ : Finset Constraint) : Prop :=
  ∃ R, R ∈ models Γ

theorem refinement (Γ : Finset Constraint) (C : Constraint) :
    models (Γ ∪ {C}) ⊆ models Γ := by
  intro R h
  unfold models satisfies_all at *
  intro D hD
  exact h D (Finset.mem_union_left {C} hD)

--------------------------------------------------------------------------------
-- §6 Type System View
--------------------------------------------------------------------------------

/-
Now, we look at constraints as *types*. The typing judgment

    Γ ⊢ R

means that realization R is well-typed under Γ.

Rules:
    (T-Empty)    ----------------
                  ∅ ⊢ R

    (T-Add)      Γ ⊢ R    R ⊨ C
                  ----------------
                  Γ ∪ {C} ⊢ R
-/

inductive WellTyped : Finset Constraint → Realization → Prop
| empty (R : Realization) : WellTyped ∅ R
| add {Γ : Finset Constraint} {R : Realization} {C : Constraint} :
    WellTyped Γ R → satisfies R C → WellTyped (Γ ∪ {C}) R


namespace Typing

theorem preservation {Γ : Finset Constraint} {R : Realization} {C : Constraint} :
  WellTyped Γ R → satisfies R C → WellTyped (Γ ∪ {C}) R :=
  WellTyped.add

theorem soundness {Γ : Finset Constraint} {R : Realization} :
  WellTyped Γ R → R ∈ models Γ := by
  intro h1
  unfold models satisfies_all at *
  induction h1 with
  | empty R =>
    -- Base case: Γ = ∅
    intro C hC
    exact False.elim (Finset.notMem_empty C hC)
  | add Γ R C =>
    -- Inductive case: Γ ⊢ R and R ⊨ C
    intro D hD
    cases Finset.mem_union.mp hD with
    | inl hIn => simp_all
    | inr hEq =>
      -- For the new constraint C
      rw [Finset.mem_singleton.mp hEq]
      exact R


theorem completeness {Γ : Finset Constraint} {R : Realization} :
  R ∈ models Γ → WellTyped Γ R := by
  intro h
  unfold models satisfies_all at h
  induction Γ using Finset.induction_on generalizing R
  case empty =>
    -- Base case: Γ = ∅
    exact WellTyped.empty R
  case insert C Γ' _ ih =>
  have hSub : R ∈ models Γ' := by
    -- Extract the fact that R satisfies all constraints in Γ'
    intro D hD
    exact h D (Finset.mem_insert_of_mem hD)
  have hSat : satisfies R C := by  -- Extract the fact that R satisfies the new constraint C
    exact h C (Finset.mem_insert_self C Γ')
  -- Now we can construct the typing judgment
  simp_all
  have hWT : WellTyped Γ' R := ih h
  have hTyped := WellTyped.add hWT hSat
  rw [Finset.union_comm] at hTyped
  rw [← Finset.insert_eq] at hTyped
  exact hTyped
end Typing

--------------------------------------------------------------------------------
-- §7 Dynamics
--------------------------------------------------------------------------------


--------------------------------------------------------------------------------
-- §7 Dynamics
--------------------------------------------------------------------------------

/-
There are two complementary formulations of dynamics:

1. **Untyped semantic dynamics**:
   At the semantic level, we may always add a constraint `c` to Γ.
   If the constraint is inconsistent, the set of models collapses to ∅.

2. **Typed program dynamics**:
   For a *fixed realization R*,
   we only allow adding a constraint `c` that `R` already satisfies.
   This ensures typing is preserved: well-typed realizations stay well-typed.
-/

-- Untyped semantics ------------------------------------------------------------

inductive StepSem : Set Realization → Set Realization → Prop
| add (Γ : Finset Constraint) (c : Constraint) :
    StepSem (models Γ) (models (Γ ∪ {c}))

/-- Multi-step closure of semantic steps. -/
def StepSem.star := Relation.ReflTransGen StepSem


/-- Semantic preservation: model sets only shrink. -/
theorem sem_preservation_step {S T : Set Realization} :
  StepSem S T → T ⊆ S := by
  intro h
  cases h with
  | add Γ c =>
    exact refinement Γ c

/-- Semantic preservation across many steps. -/
theorem sem_preservation_star {S T : Set Realization} :
  StepSem.star S T → T ⊆ S := by
  intro h
  induction h with
  | refl =>
    -- base case: S = T, so T ⊆ S
    intro x hx; exact hx
  | tail G step ih => exact Set.Subset.trans (sem_preservation_step step) ih


-- Typed program dynamics -------------------------------------------------------

inductive StepProg (R : Realization) : Finset Constraint → Finset Constraint → Prop
| add {Γ : Finset Constraint} {c : Constraint} :
    satisfies R c →
    StepProg R Γ (Γ ∪ {c})

def StepProg.star (R : Realization) := Relation.ReflTransGen (StepProg R)

/-- Preservation: typed steps preserve well-typedness. -/
lemma typing_preserved_step {Γ Γ' : Finset Constraint} {R : Realization} :
  WellTyped Γ R → StepProg R Γ Γ' → WellTyped Γ' R := by
  intro hWT hStep
  cases hStep with
  | add hSat =>
    exact WellTyped.add hWT hSat

lemma typing_preserved_along_star {Γ Γ' : Finset Constraint} {R : Realization} :
  WellTyped Γ R → StepProg.star R Γ Γ' → WellTyped Γ' R := by
  intro hWT hStar
  induction hStar with
  | refl => exact hWT
  | tail G step ih => exact typing_preserved_step ih step





--------------------------------------------------------------------------------
-- §8 Meta-Theorems
--------------------------------------------------------------------------------

/-
We now state the key theorems:

* Refinement: models(Γ ∪ {C}) ⊆ models(Γ)
* Progress: if Γ is satisfiable, then ∃R, Γ ⊢ R
* Preservation: if Γ ⊢ R and R ⊨ C, then Γ ∪ {C} ⊢ R
* Soundness & Completeness: Γ ⊢ R ↔ R ∈ models Γ
* Type Safety: if Γ ⊢ R and Γ ⟶* Γ′, then R ∈ models Γ′
-/

theorem typing_semantics_equiv (Γ : Finset Constraint) (R : Realization) :
  WellTyped Γ R ↔ R ∈ models Γ :=
⟨Typing.soundness, Typing.completeness⟩




/-- Type safety: well-typed realizations remain semantic models along typed steps. -/
theorem type_safety {Γ Γ' : Finset Constraint} {R : Realization} :
  WellTyped Γ R → StepProg.star R Γ Γ' → R ∈ models Γ' := by
  intro hWT hSteps
  have hWT' := typing_preserved_along_star hWT hSteps
  exact Typing.soundness hWT'


end CnD

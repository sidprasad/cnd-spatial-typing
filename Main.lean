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

-- TODO: Maybe CoreConstraint is bad nomenclature. Really it is LayoutConstraint (or Relative Orientation Constraint)
/-- Core constraints are binary geometric relations. -/
inductive CoreConstraint
| left                  (a b : Atom)
| above                 (a b : Atom)
| horizontally_aligned  (a b : Atom)
| vertically_aligned    (a b : Atom)
deriving BEq, DecidableEq


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

def satisfies_core_constraint (R : Realization) (c : CoreConstraint) : Prop :=
  match c with
  | CoreConstraint.left a b                 => atom_left_of a b R
  | CoreConstraint.above a b                => atom_above a b R
  | CoreConstraint.horizontally_aligned a b => atom_horizontally_aligned a b R
  | CoreConstraint.vertically_aligned a b   => atom_vertically_aligned a b R


def satisfies_all_core_constraints (R : Realization) (cs : Finset CoreConstraint) : Prop :=
  ∀ c ∈ cs, satisfies_core_constraint R c

---------------------------------------------------------------------------------
-- §3 Structural Relations: Grouping and Cyclic Order
--------------------------------------------------------------------------------

/-
Beyond primitive binary relations, we also want to describe **structural
constraints** that involve sets or sequences of atoms.

Two key forms:
  * Grouping: a set of atoms must be enclosed in a bounding rectangle,
    with no extraneous atoms inside.
  * Cyclic order: a sequence of atoms must be arranged around a circle,
    up to rotation. Cyclic order is expressed entirely in terms of the
    primitive constraints (left, above, alignment).
-/
inductive StructuralConstraint
| group   (S : Finset Atom)
| cyclic  (L : List Atom)
deriving BEq, DecidableEq

-- Grouping --------------------------------------------------------------

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


-- Cyclic order -----------------------------------------------------------

open Real
noncomputable def angleStep (n : Nat) : ℝ := (2 * π ) / n

/--
Generate the core constraints implied by placing two atoms
at given angles on the unit circle.
-/
noncomputable def constraints_from_angles
  (a b : Atom) (θa θb : ℝ) : Finset CoreConstraint :=
  let xa := Real.cos θa
  let ya := Real.sin θa
  let xb := Real.cos θb
  let yb := Real.sin θb
  ∅
  -- horizontal relation
  |> (if xa < xb then (· ∪ {CoreConstraint.left a b})
      else if xa > xb then (· ∪ {CoreConstraint.left b a})
      else (· ∪ {CoreConstraint.vertically_aligned a b}))
  -- vertical relation
  |> (if ya < yb then (· ∪ {CoreConstraint.above a b})
      else if ya > yb then (· ∪ {CoreConstraint.above b a})
      else (· ∪ {CoreConstraint.horizontally_aligned a b}))


/--
Constraints for perturbation `k` of a cycle of atoms.
The relative positions of atoms is based on how they might be placed evenly around
the unit circle, rotated by offset `k`.
-/
noncomputable def perturbation_constraints (L : List Atom) (k : Nat) : Finset CoreConstraint :=
  let n := L.length
  let step := angleStep n
  let angles : List ℝ := (List.range n).map (fun i => (i + k : ℕ) * step)
  -- accumulate all constraints from consecutive pairs
  (List.range n).foldl
    (fun acc i =>
      let a := L[i]!
      let b := L[((i+1) % n)]!  -- wrap-around
      acc ∪ constraints_from_angles a b (angles[i]!) (angles[((i+1) % n)]!))
    ∅


/--
Atoms satisfy a cyclic constraint if there exists some perturbation
(offset k) such that all constraints induced by that perturbation hold.
-/

def satisfies_perturbation (R : Realization) (L : List Atom) (k : Nat) : Prop :=
  satisfies_all_core_constraints R (perturbation_constraints L k)


def atoms_cyclic (L : List Atom) (R : Realization) : Prop :=
  ∃ k, k < L.length ∧ satisfies_perturbation R L k




/--
Another way to think about this is that there is a large finite disjunction
of constraint sets, that must be satisfied for cyclic order.


TODO: PROVE THIS.
-/
lemma atoms_cyclic_iff_big_or (L : List Atom) (R : Realization) :
  atoms_cyclic L R ↔
    (List.range L.length).foldr (fun k acc => satisfies_perturbation R L k ∨ acc) False :=
by
  constructor
  · -- → direction
    intro ⟨k, hk, hSat⟩
    sorry
    -- k is in List.range L.length
    -- have : k ∈ List.range L.length := List.mem_range.mpr hk
    -- -- so the big OR holds
    -- induction List.range L.length with
    -- | nil => cases this
    -- | cons k0 ks ih =>
    --   simp [List.foldr]
    --   cases this with
    --   | inl hEq =>
    --     subst hEq
    --     exact Or.inl hSat
    --   | inr hIn =>
    --     exact Or.inr (ih hIn)
  · -- ← direction
    intro h
    sorry
    -- induction List.range L.length with
    -- | nil => simp at h
    -- | cons k0 ks ih =>
    --   simp [List.foldr] at h
    --   cases h with
    --   | inl hSat =>
    --     exact ⟨k0, Nat.zero_lt_succ _, hSat⟩
    --   | inr hRest =>
    --     rcases ih hRest with ⟨k, hk, hSat⟩
    --     exact ⟨k+1, Nat.succ_lt_succ hk, hSat⟩



--------------------------------------------------------------------------------
-- §4 Constraint Language
--------------------------------------------------------------------------------

/-
The core constraint language for CnD: atomic spatial requirements
over atoms, plus grouping.
-/

/--
The full constraint language is the disjoint union of core and structural
constraints. This is like "inheritance": every core or structural constraint
can be lifted into a `Constraint`.
-/
inductive Constraint
| core       (c : CoreConstraint)
| structural (s : StructuralConstraint)
deriving BEq, DecidableEq






--------------------------------------------------------------------------------
-- §5 Semantics View
--------------------------------------------------------------------------------

/-
Constraints can be read as truth conditions: they denote sets of realizations.
-/



/--
Interpretation of constraints: what it means for a realization `R`
to satisfy a single constraint.
-/
def satisfies (R : Realization) : Constraint → Prop
| Constraint.core c => satisfies_core_constraint R c
| Constraint.structural s =>
  match s with
  | StructuralConstraint.group S  => atoms_grouped S R
  | StructuralConstraint.cyclic L => atoms_cyclic L R

/--
Judgment: `SatisfiesAll R Γ` means realization `R` satisfies all constraints in list `Γ`.
This is defined inductively so that `cyclic` can branch existentially.
-/
inductive SatisfiesAll : Realization → List Constraint → Prop
| nil (R) :
    SatisfiesAll R []
| core (R c Γ) :
    satisfies_core_constraint R c →
    SatisfiesAll R Γ →
    SatisfiesAll R (Constraint.core c :: Γ)
| group (R S Γ) :
    atoms_grouped S R →
    SatisfiesAll R Γ →
    SatisfiesAll R (Constraint.structural (StructuralConstraint.group S) :: Γ)
| cyclic (R L Γ k) :
    k < L.length →
    satisfies_perturbation R L k →
    SatisfiesAll R Γ →
    SatisfiesAll R (Constraint.structural (StructuralConstraint.cyclic L) :: Γ)

lemma satisfies_all_append_left {R : Realization} {Γ Δ : List Constraint} :
  SatisfiesAll R (Γ ++ Δ) → SatisfiesAll R Γ := by
  induction Γ generalizing R Δ
  case nil =>
    intro _
    exact SatisfiesAll.nil R
  case cons C Γ ih =>
    intro h
    cases C with
    | core c =>
      cases h with
      | core _ hc z hΓΔ =>
        -- IH gives SatisfiesAll R Γ from hΓΔ
        have hΓ := ih hΓΔ
        exact SatisfiesAll.core R c Γ z hΓ

    | structural s =>
      cases s with
      | group S =>
        cases h with
        | group _ hg z hΓΔ =>
          have hΓ := ih hΓΔ
          exact SatisfiesAll.group hg hΓ
      | cyclic L =>
        cases h with
        | cyclic _ _ k hk hPert hΓΔ =>
          have hΓ := ih hΓΔ
          exact SatisfiesAll.cyclic R L Γ k hk hPert hΓ










/--
Satisfaction of a finite set of constraints:
defined by picking any enumeration (`toList`) and using `SatisfiesAll`.
TODO: Prove Order invariance.
-/
def satisfies_all (R : Realization) (Γ : Finset Constraint) : Prop :=
  SatisfiesAll R Γ.toList





lemma satisfies_all_perm {Γ : List Constraint} {Γ' : List Constraint} {R : Realization} :
  Γ.Perm Γ' → (SatisfiesAll R Γ ↔ SatisfiesAll R Γ') := by
  intro hperm
  induction hperm generalizing R
  case nil =>
    -- Base case: both lists are empty
    simp [SatisfiesAll.nil]
  case cons x l l' hperm ih =>
    -- Inductive case: x is added to both lists
    cases x with
    | core c => sorry
    | structural s => sorry

  case swap x y l => sorry
  case trans l₁ l₂ l₃ h₁₂ h₂₃ ih₁₂ ih₂₃ => sorry

lemma satisfies_all_finset_eq (Γ : Finset Constraint) (R : Realization) :
  satisfies_all R Γ = SatisfiesAll R Γ.toList :=
  rfl


/--
Maybe Γ is the wrong letter to use here.
Its the program, not the env.

-/
def models (Γ : Finset Constraint) : Set Realization :=
  { R | satisfies_all R Γ }

def satisfiable (Γ : Finset Constraint) : Prop :=
  ∃ R, R ∈ models Γ




-- -- THIS SHOULD FAIL NOW. Isn't quite the refinement thm we want.
-- theorem refinement (Γ : Finset Constraint) (C : Constraint) :
--     models (Γ ∪ {C}) ⊆ models Γ := by
--   intro R h
--   unfold models satisfies_all at *
--   intro D hD
--   exact h D (Finset.mem_union_left {C} hD)






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

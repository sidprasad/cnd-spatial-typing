# CnD: Constraints as Semantics *and* as a Type System

CnD constraints can be understood in two complementary ways:

---

## 1. **The Semantics View**

Constraints directly describe what a layout means.

* Constraint set `Γ` = a program/specification.
* Realization `R` = (a concrete placement of atoms that satisfies a set of spatial constraints).
* Semantics:

  $$
  \llbracket Γ \rrbracket = \{ R \mid ∀ C ∈ Γ, \; R \models C \}
  $$

  The denotation of `Γ` is the set of all realizations that satisfy its constraints.
* **Key property (Refinement):**
  Adding a new constraint narrows the set of models:

  $$
  \llbracket Γ ∪ \{C\} \rrbracket \subseteq \llbracket Γ \rrbracket
  $$

This view emphasizes **what constraints mean**: they are logical conditions over diagrams, and realizations are their solutions.

---

## 2. **The Type System View**

Constraints also act as **types** in a spatial type system.

* **Constraints are types.**
* **Constraint sets `Γ` are typing contexts.**
* **Typing judgment:**

  ```
  Γ ⊢ R
  ```

  means “realization `R` has type `Γ`.”
* **Typing rules:**

  ```
  -----------  (T-Empty)
  ∅ ⊢ R

  Γ ⊢ R     R ⊨ C
  ---------------- (T-Add)
  Γ ∪ {C} ⊢ R
  ```
* **Meta-theorems (Progress & Preservation):**

  * *Progress:* If `Γ` is satisfiable, then there exists some well-typed realization.
  * *Preservation:* If `Γ ⊢ R` and `Γ ⟶ Γ ∪ {C}`, then `Γ ∪ {C} ⊢ R`.
* **Soundness:**

  ```
  Γ ⊢ R  ⇒  R ∈ ⟦Γ⟧
  ```

  i.e. well-typed realizations are always valid models.

This view emphasizes **how constraints discipline diagrams**: they form a lightweight type system that guarantees well-formed layouts.

### Questions:

- How do unsat layouts show up here? A static error should be when no realization exists that can satisfy the constraint set.


---

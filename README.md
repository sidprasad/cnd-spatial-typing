# CnD: Constraints as Semantics *and* as a Type System

**Note:** For all formal definitions, proofs, and the complete source of truth, see [`Main.lean`](./Main.lean).

---

## Overview

CnD constraints can be understood in two complementary ways:

1. **The Semantics View**: Constraints describe the meaning of a layout by specifying the set of realizations that satisfy them.

2. **The Type System View**: Constraints act as types in a spatial type system, ensuring well-formedness of realizations.

For detailed explanations, typing rules, and meta-theorems (e.g., Progress, Preservation, Soundness), refer to [`Main.lean`](./Main.lean).

---

## Questions

- How do unsatisfiable layouts manifest in this system? A static error should occur when no realization exists that satisfies the constraint set.
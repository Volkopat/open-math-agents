import Mathlib

/-!
# A generalization of Vizing's Theorem?

Source: https://www.openproblemgarden.org/op/a_generalization_of_vizings_theorem
Credit: @ishaanzee

**Conjecture.** Let `H` be a simple `d`-uniform hypergraph, and assume that every set of `d - 1`
points is contained in at most `r` edges. Then there exists an `(r + d - 1)`-edge-coloring so that
any two edges which share `d - 1` vertices have distinct colors.

Vizing's theorem is the case `d = 2`.

Formalization:
* A simple `d`-uniform hypergraph on a finite vertex set `V` is a finite set `E` of `d`-element
  subsets of `V` (no repeated edges). We take `d ≥ 2`, the range where the statement is meant
  (`d = 2` being Vizing's theorem).
* "Every set of `d - 1` points is contained in at most `r` edges": for every `T` with `|T| = d - 1`,
  at most `r` edges contain `T`.
* An `(r + d - 1)`-edge-coloring is `c : Finset V → Fin (r + d - 1)` (only its values on edges
  matter); two distinct edges sharing `d - 1` vertices are those with `|e ∩ e'| = d - 1`.
-/

namespace OMA.S_opg_a_generalization_of_vizings_theorem

/-- **Conjecture** (hypergraph Vizing). -/
theorem main : ∀ (V : Type) [Fintype V] [DecidableEq V] (d r : ℕ) (E : Finset (Finset V)),
    2 ≤ d → (∀ e ∈ E, e.card = d) →
    (∀ T : Finset V, T.card = d - 1 → (E.filter fun e => T ⊆ e).card ≤ r) →
    ∃ c : Finset V → Fin (r + d - 1), ∀ e ∈ E, ∀ e' ∈ E, e ≠ e' → (e ∩ e').card = d - 1 →
      c e ≠ c e' := by
  sorry

end OMA.S_opg_a_generalization_of_vizings_theorem

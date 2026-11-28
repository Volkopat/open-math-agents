import Mathlib

/-!
# A gadget for 4-regular uniquely Hamiltonian graphs

Source: https://mathoverflow.net/questions/261273 (CC BY-SA 4.0).

A conjecture (Sheehan's) says there is no `r`-regular uniquely Hamiltonian graph for `r > 2`; the case
`r = 4` is of special interest. The asker asks whether there is a gadget: a finite simple connected graph
with two vertices `u, v` of degree 3, all others of degree 4, and exactly one Hamiltonian `u`–`v` path.
Two copies joined by `u₁u₂` and `v₁v₂` would be a 4-regular uniquely Hamiltonian graph, against the
conjecture. A computer search found none on up to 12 vertices.

We state that no such gadget exists (the answer predicted by the conjecture).

Formalization notes:
* Degrees are `Nat.card` of neighbor sets (so no decidability instance is needed).
* A Hamiltonian `u`–`v` path is a walk from `u` to `v` visiting every vertex exactly once
  (`SimpleGraph.Walk.IsHamiltonian`); "exactly one" is `∃!`.
-/

namespace OMA.S_mo_261273

/-- No connected graph with degrees `3, 3, 4, …, 4` has a unique Hamiltonian path between its two
degree-3 vertices. -/
theorem main : ¬ ∃ (n : ℕ) (G : SimpleGraph (Fin n)) (u v : Fin n),
    G.Connected ∧ u ≠ v ∧ Nat.card (G.neighborSet u) = 3 ∧ Nat.card (G.neighborSet v) = 3 ∧
      (∀ w, w ≠ u → w ≠ v → Nat.card (G.neighborSet w) = 4) ∧
      ∃! p : G.Walk u v, p.IsHamiltonian := by
  sorry

end OMA.S_mo_261273

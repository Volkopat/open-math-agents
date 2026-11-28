import Mathlib

/-!
# Ryser's conjecture

Source: https://en.wikipedia.org/wiki/Ryser's_conjecture
Credit: @mattdorman

The source states Ryser's conjecture relating the maximum matching size and minimum transversal
size in hypergraphs: for every `r`-partite `r`-uniform hypergraph, `τ ≤ (r - 1) ν`, where `ν` is
the maximum number of pairwise disjoint edges and `τ` the minimum number of vertices meeting
every edge.

Reading used here: `r ≥ 2`; the hypergraph is a finite family `H` of edges on a finite vertex
type `V` with a partition `part : V → Fin r` into `r` parts, every edge having exactly one vertex
in each part. Because `ν` is a maximum and `τ` a minimum, `τ ≤ (r - 1) ν` holds exactly when
some transversal `T` and some matching `M ⊆ H` satisfy `|T| ≤ (r - 1) |M|`; the statement is
written in that form.
-/

namespace OMA.S_wp_ryser_s_conjecture

theorem main :
    ∀ (r : ℕ), 2 ≤ r → ∀ (V : Type) [Fintype V] [DecidableEq V] (part : V → Fin r)
      (H : Finset (Finset V)),
      (∀ e ∈ H, ∀ i : Fin r, ∃! v, v ∈ e ∧ part v = i) →
        ∃ T : Finset V, (∀ e ∈ H, (e ∩ T).Nonempty) ∧
          ∃ M ⊆ H, (∀ e ∈ M, ∀ f ∈ M, e ≠ f → Disjoint e f) ∧ T.card ≤ (r - 1) * M.card := by
  sorry

end OMA.S_wp_ryser_s_conjecture

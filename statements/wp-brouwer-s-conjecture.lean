import Mathlib

/-!
# Brouwer's conjecture

Source: https://en.wikipedia.org/wiki/Brouwer%27s_conjecture
Credit: @shc261392

Brouwer's conjecture: let `G` be a simple graph with `m` edges whose Laplacian eigenvalues are
`λ₁ ≥ λ₂ ≥ ⋯ ≥ λₙ`. Then for every `t ∈ {1, …, n}`,
`λ₁ + ⋯ + λₜ ≤ m + t (t + 1) / 2`.

Reading used here:
* `G` is a finite simple graph; its Laplacian is Mathlib's `G.lapMatrix ℝ` (degree matrix minus
  adjacency matrix), which is Hermitian (`SimpleGraph.isHermitian_lapMatrix`).
* `eigenvalues₀` lists the eigenvalues with multiplicity in decreasing order, indexed by
  `Fin (Fintype.card V)`; the sum of the `t` largest is the sum over
  `i : Fin t`, cast into `Fin (Fintype.card V)` by `Fin.castLE`.
* `m` is `G.edgeFinset.card`.
-/

namespace OMA.S_wp_brouwer_s_conjecture

theorem main :
    ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
      ∀ (t : ℕ) (ht : t ≤ Fintype.card V), 1 ≤ t →
        ∑ i : Fin t, (G.isHermitian_lapMatrix (R := ℝ)).eigenvalues₀ (Fin.castLE ht i) ≤
          (G.edgeFinset.card : ℝ) + (t : ℝ) * (t + 1) / 2 := by
  sorry

end OMA.S_wp_brouwer_s_conjecture

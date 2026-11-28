import Mathlib

/-!
# Nordhaus–Gaddum upper bound for the number of dominating sets

Source: https://arxiv.org/abs/1808.05576, Conjecture 1.2 (Keough and Shane)
Credit: @pyaf

A dominating set of G is a vertex set S such that every vertex lies in S or
is adjacent to a vertex of S; ∂(G) is the number of dominating sets. The
conjecture: every graph G on n vertices satisfies
∂(G) + ∂(Gᶜ) ≤ 2(2^⌊n/2⌋ − 1)(2^⌈n/2⌉ − 1) + 2, the value attained by the
complete balanced bipartite graph. Here ⌈n/2⌉ = n − ⌊n/2⌋.
-/

namespace OMA.S_arxiv_1808_05576

/-- The number of dominating sets of G. -/
def numDom {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] : ℕ :=
  (Finset.univ.filter (fun S : Finset (Fin n) => ∀ v, v ∈ S ∨ ∃ u ∈ S, G.Adj v u)).card

theorem main : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
    numDom G + numDom Gᶜ ≤ 2 * (2 ^ (n / 2) - 1) * (2 ^ (n - n / 2) - 1) + 2 := by
  sorry

end OMA.S_arxiv_1808_05576

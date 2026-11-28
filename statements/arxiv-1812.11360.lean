import Mathlib

/-!
# Signatures of the odd prisms P(2n+1, 1) up to switching

Source: https://arxiv.org/abs/1812.11360, conjecture in the abstract (Deepak)
Credit: @pyaf

A signature of a graph G is a set Σ of its edges (the negative edges).
Switching at a vertex set X negates every edge with exactly one end in X.
The generalised Petersen graph P(2n+1, 1) is the prism C₂ₙ₊₁ □ K₂.
Conjecture: for every n ≥ 1, every signature of P(2n+1, 1) is switching
equivalent to a signature with at most n + 1 edges.

Later work: arXiv:2511.15226 bounds the frustration index of 2-edge-connected
subcubic graphs on N vertices by N/3, which gives (4n+2)/3 here and settles
only n ≤ 3. Searches for signed generalised Petersen graphs and for the
frustration index of prisms found no resolution.
-/

namespace OMA.S_arxiv_1812_11360

open SimpleGraph

/-- The generalised Petersen graph P(N, 1): outer and inner N-cycles joined by spokes. -/
abbrev prism (N : ℕ) : SimpleGraph (Fin N × Fin 2) := cycleGraph N □ ⊤

/-- The negative edges after switching the signature S at the vertex set X:
an edge uv stays as it was when u, v lie on the same side of X and flips otherwise. -/
def switch {V : Type*} (G : SimpleGraph V) (S : Set (Sym2 V)) (X : Set V) : Set (Sym2 V) :=
  {e | e ∈ G.edgeSet ∧ ∃ u v, e = s(u, v) ∧ (e ∈ S ↔ (u ∈ X ↔ v ∈ X))}

theorem main : ∀ n ≥ 1, ∀ S ⊆ (prism (2 * n + 1)).edgeSet,
    ∃ X : Set (Fin (2 * n + 1) × Fin 2), (switch (prism (2 * n + 1)) S X).ncard ≤ n + 1 := by
  sorry

end OMA.S_arxiv_1812_11360

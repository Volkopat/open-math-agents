import Mathlib

namespace OMA.S_arxiv_2404_04039

/-- A vertex `v` of a graph `G` is a boundary vertex if there exists another vertex `u ≠ v`
such that no neighbor `w` of `v` is strictly farther from `u` than `v` is. -/
def IsBoundaryVertex {n : ℕ} (G : SimpleGraph (Fin n)) (v : Fin n) : Prop :=
  ∃ u : Fin n, u ≠ v ∧ ∀ w : Fin n, G.Adj v w → G.dist u w ≤ G.dist u v

/-- The boundary `∂(G)` of a graph `G`. -/
def boundarySet {n : ℕ} (G : SimpleGraph (Fin n)) : Set (Fin n) :=
  { v : Fin n | IsBoundaryVertex G v }

/-- Conjecture (Cáceres & Pelayo, arXiv:2404.04039; later refuted by the authors in
arXiv:2506.02652): Every connected graph `G` on `n ≥ 2` vertices is uniquely determined up
to isomorphism by its order `n`, its boundary `∂(G)`, and its boundary distance matrix
`(d_G(x, y))_{x, y ∈ ∂(G)}`. -/
theorem main :
    ∀ (n : ℕ), 2 ≤ n →
      ∀ (G₁ G₂ : SimpleGraph (Fin n)),
        G₁.Connected → G₂.Connected →
        boundarySet G₁ = boundarySet G₂ →
        (∀ x ∈ boundarySet G₁, ∀ y ∈ boundarySet G₁, G₁.dist x y = G₂.dist x y) →
        Nonempty (G₁ ≃g G₂) := by
  sorry

end OMA.S_arxiv_2404_04039

import Mathlib

/-!
# Lower bounds for the Randić index in terms of matching number

Akbari, Ghasemi Nezhad, Ghazizadeh, Haslegrave and Tohidi, Conjecture 9,
arXiv:2402.12884v2, page 9. Credit: @ryansolves
-/

namespace OMA.S_arxiv_2402_12884

variable {n : ℕ}

/-- Both orientations of every undirected edge. -/
noncomputable def darts (G : SimpleGraph (Fin n)) : Finset (Fin n × Fin n) := by
  classical exact Finset.univ.filter fun e => G.Adj e.1 e.2

/-- Half the sum over oriented edges counts each undirected edge once. -/
noncomputable def randic (G : SimpleGraph (Fin n)) : ℝ := by
  classical exact (∑ e ∈ darts G, (Real.sqrt ((G.degree e.1 : ℝ) * G.degree e.2))⁻¹) / 2

/-- A matching keeps both orientations of each selected edge. A vertex
therefore occurs as first endpoint at most once exactly when its degree in
the selected undirected subgraph is at most one. -/
def isMatching (G : SimpleGraph (Fin n)) (M : Finset (Fin n × Fin n)) : Prop :=
  M ⊆ darts G ∧ (∀ e ∈ M, e.swap ∈ M) ∧ Set.InjOn Prod.fst (M : Set (Fin n × Fin n))

/-- Each matching has twice as many oriented edges as undirected edges. -/
noncomputable def matchingNumber (G : SimpleGraph (Fin n)) : ℕ := by
  classical exact ((darts G).powerset.filter (isMatching G)).sup fun M => M.card / 2

theorem main :
    ∃ c : ℝ, 0 < c ∧ ∀ (n : ℕ) (G : SimpleGraph (Fin n)),
      c * (matchingNumber G : ℝ) ^ (2 / 3 : ℝ) ≤ randic G := by
  sorry

end OMA.S_arxiv_2402_12884

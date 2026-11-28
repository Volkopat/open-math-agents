import Mathlib

namespace OMA.S_arxiv_2101_11233

open SimpleGraph

theorem main :
    ∀ (n : ℕ), 2 ≤ n →
    ∀ (c : Sym2 (Fin n) → ℤ),
      (∀ e ∈ (⊤ : SimpleGraph (Fin n)).edgeFinset, c e = 1 ∨ c e = -1) →
      (∑ e ∈ (⊤ : SimpleGraph (Fin n)).edgeFinset, c e) = 0 →
    ∀ (F : SimpleGraph (Fin n)) [DecidableRel F.Adj],
      F.IsAcyclic →
      1 ≤ F.maxDegree →
      ∃ (F' : SimpleGraph (Fin n)) (_ : DecidableRel F'.Adj),
        Nonempty (F ≃g F') ∧
        (|(∑ e ∈ F'.edgeFinset, c e : ℤ)| : ℝ) ≤ ((F.maxDegree : ℝ) - 1) / 2 := by
  sorry

end OMA.S_arxiv_2101_11233

import OMAStatements.S_arxiv_1804_07104
import Mathlib

/- Construct the circle from complementary odd-even pairs of sum 2n+1.
Advance the odd entry by a stride 2s cyclically among the odds. Coprimality
of the stride index s with n gives a single tour, and its crossing edges
have sums 2s+1 and 2n+2s+1. For s=1 this includes the twin-prime case. -/
namespace OMA.R_arxiv_1804_07104_R1

def H1 : Prop :=
  ∀ n s : ℕ, 2 ≤ n → s < n → n.Coprime s →
    (2 * n + 1).Prime → (2 * s + 1).Prime → (2 * n + 2 * s + 1).Prime →
    ∃ a : Fin (2 * n) ≃ Fin (2 * n),
      ∀ k : Fin (2 * n), ((a k).val + 1 + ((a (finRotate (2 * n) k)).val + 1)).Prime

def H2 : Prop :=
  ∀ n : ℕ, 2 ≤ n →
    (¬ ∃ s < n, n.Coprime s ∧ (2*n+1).Prime ∧ (2*s+1).Prime ∧ (2*n+2*s+1).Prime) →
    ∃ a : Fin (2*n) ≃ Fin (2*n),
      ∀ k : Fin (2*n), ((a k).val + 1 + ((a (finRotate (2*n) k)).val + 1)).Prime

theorem main : H1 → H2 → type_of% @OMA.S_arxiv_1804_07104.main := by
  intro construct remaining n hn
  by_cases h : ∃ s < n, n.Coprime s ∧ (2*n+1).Prime ∧ (2*s+1).Prime ∧ (2*n+2*s+1).Prime
  · obtain ⟨s, hs, cop, center, low, high⟩ := h
    exact construct n s hn hs cop center low high
  · exact remaining n hn h

end OMA.R_arxiv_1804_07104_R1

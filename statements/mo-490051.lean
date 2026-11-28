import Mathlib

/-! Source: https://mathoverflow.net/questions/490051 -/

open scoped BigOperators

namespace OMA.S_mo_490051

/-- The cardinality-weighted inequality (2) for a union-closed family. -/
theorem main :
    ∀ (n : ℕ) (F : Finset (Finset (Fin n))), 0 < n →
      (∀ i : Fin n, ∃ A ∈ F, i ∈ A) →
      (∀ A ∈ F, ∀ B ∈ F, A ∪ B ∈ F) →
      ∃ k : Fin n,
        (∑ A ∈ F.filter (fun A => k ∉ A), (A.card + 1)) ≤
          ∑ A ∈ F.filter (fun A => k ∈ A), A.card := by
  sorry

end OMA.S_mo_490051

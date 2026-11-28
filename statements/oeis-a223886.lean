import Mathlib

namespace OMA.S_oeis_a223886

theorem main :
    ∀ k j : ℕ, 0 < k → 0 < j →
      ∃ N : ℕ, ∀ p : ℕ, Nat.Prime p → N < p →
        k * p ^ 3 ∣ (Nat.choose (j * k * p) (j * p) - Nat.choose (k * j) j) := by
  sorry

end OMA.S_oeis_a223886

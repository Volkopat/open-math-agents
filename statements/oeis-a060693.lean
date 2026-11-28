import Mathlib

namespace OMA.S_oeis_a060693

theorem main :
    ∀ n : ℕ,
      ∑ k ∈ Finset.range (n + 1),
        (-1 : ℤ) ^ k *
          ((Nat.choose n k * Nat.choose (2 * n - k) n / (n + 1 - k) : ℕ) : ℤ) *
          ((n + 1 - k : ℕ) : ℤ) ^ 2 =
        1 + (n : ℤ) + (n : ℤ) ^ 2 := by
  sorry

end OMA.S_oeis_a060693

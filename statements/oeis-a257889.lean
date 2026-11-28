import Mathlib

namespace OMA.S_oeis_a257889

theorem main :
    ∀ (a b : ℕ → ℤ),
      a 0 = 1 →
      a 1 = 1 →
      (∀ n : ℕ, b n = PowerSeries.coeff n (PowerSeries.mk a ^ 2)) →
      (∀ n : ℕ, 1 ≤ n → a (2 * n) = a n * b n ∧ a (2 * n + 1) = a n * b (n + 1)) →
      ∀ n : ℕ, (5 : ℤ) ∣ a (3 * 2 ^ n) := by
  sorry

end OMA.S_oeis_a257889

import Mathlib

namespace OMA.S_oeis_a326602

theorem main :
    ∀ (a : ℕ → ℤ) (U : ℕ → PowerSeries ℤ),
      (∀ n : ℕ, U n * (1 + PowerSeries.X ^ (2 * n + 1)) = 1) →
      (∀ k : ℕ,
        a k =
          ∑ n ∈ Finset.range (2 * k + 1),
            PowerSeries.coeff (2 * k)
              ((PowerSeries.X ^ (2 * n) + PowerSeries.X) ^ n * U n ^ (n + 1))) →
      ∀ n : ℕ, Odd (a n) ↔ IsSquare n := by
  sorry

end OMA.S_oeis_a326602

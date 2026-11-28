import Mathlib

namespace OMA.S_oeis_a078534

theorem main :
    ∀ (n : ℕ), 2 ≤ n →
    ∀ (A : PowerSeries ℚ),
      PowerSeries.coeff 0 A = 1 →
      A ^ n - (n : PowerSeries ℚ) ^ 2 * PowerSeries.X * A ^ (n + 1) = 1 →
      PowerSeries.coeff (n - 1) A = (n : ℚ) ^ (2 * n - 3) ∧
      PowerSeries.coeff (2 * n - 1) A = (n : ℚ) ^ (4 * n - 2) := by
  sorry

end OMA.S_oeis_a078534

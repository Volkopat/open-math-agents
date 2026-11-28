import Mathlib

namespace OMA.S_oeis_a378840

theorem main :
    ∀ (A C B : PowerSeries ℚ),
      A = C ^ 3 →
      PowerSeries.coeff 0 C = 1 →
      A = (1 + PowerSeries.X * C ^ 4 * (1 + C)) ^ 3 →
      B = 1 + PowerSeries.X * B ^ 4 + PowerSeries.X * B ^ 5 →
      A = B ^ 3 := by
  sorry

end OMA.S_oeis_a378840

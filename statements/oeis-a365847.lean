import Mathlib

namespace OMA.S_oeis_a365847

theorem main :
    ∀ (A B : PowerSeries ℚ),
      (PowerSeries.X * A) * (1 - PowerSeries.X * A) ^ 4 =
        PowerSeries.X * (1 + PowerSeries.X * A) ^ 4 →
      B = 1 + PowerSeries.X * B ^ 4 + PowerSeries.X * B ^ 5 →
      A = B ^ 4 := by
  sorry

end OMA.S_oeis_a365847

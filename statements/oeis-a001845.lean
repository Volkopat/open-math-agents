import Mathlib

/-!
# OEIS A001845: Generating function of the centered octahedral numbers

Source: https://oeis.org/A001845
Credit: @justusklocke-cloud
-/

namespace OMA.S_oeis_a001845

/-- The centered octahedral numbers, with the index starting at zero. -/
def a (n : ℕ) : ℚ :=
  (2 * (n : ℚ) + 1) * (2 * (n : ℚ) ^ 2 + 2 * (n : ℚ) + 3) / 3

/-- Plouffe's generating function, with the unit denominator cleared. -/
theorem main : PowerSeries.mk a * (1 - PowerSeries.X) ^ 4 = (1 + PowerSeries.X) ^ 3 := by
  sorry

end OMA.S_oeis_a001845

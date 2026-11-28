import Mathlib

/-!
# The generating function of OEIS A119574

Harvey P. Dale proposed this identity in June 2024. Sela Fried proved it in
October 2024. Source: https://oeis.org/A119574 (OEIS Foundation, CC BY-SA 4.0).
Credit: @connoranderson
-/

namespace OMA.S_oeis_a119574

open PowerSeries

/-- The sequence with offset zero, viewed in the coefficient field ℚ. -/
def a (n : ℕ) : ℚ :=
  ((2*n).choose n : ℚ) * ((n : ℚ)+2)^2 / ((n : ℚ)+1)

/-- Dale's generating function with its denominator cleared. The unit constant
coefficient specifies the square root used for the power (1-4X)^(3/2). -/
theorem main : ∃ S : PowerSeries ℚ,
    constantCoeff S = 1 ∧ S^2 = 1 - 4*X ∧
      2*X*S^3*PowerSeries.mk a = -1 + 14*X - 36*X^2 + S^3 := by
  sorry

end OMA.S_oeis_a119574

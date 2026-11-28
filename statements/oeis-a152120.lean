import Mathlib

/-!
# The trigonometric product A152120

Source: https://oeis.org/A152120
Credit: @Iraeeee
-/

namespace OMA.S_oeis_a152120

noncomputable def factor (n j : ℕ) : ℝ := 2+3*Real.cos ((j:ℝ)*Real.pi/n)^2

noncomputable def a (n : ℕ) : ℝ :=
  2^n * ∏ j ∈ Finset.range ((n-1)/2), factor n (j+1)

/-- Cross-multiplied ordinary generating function. Its denominator has constant term one. -/
def generating (f : ℕ → ℝ) : Prop :=
  let X : PowerSeries ℝ := PowerSeries.X
  PowerSeries.mk f * (1 - PowerSeries.C 14*X^2 + PowerSeries.C 9*X^4) =
    1 + PowerSeries.C 2*X - PowerSeries.C 10*X^2 - PowerSeries.C 6*X^3 + PowerSeries.C 9*X^4

theorem main : (∀ n : ℕ, 4 < n → a n = 14*a (n-2)-9*a (n-4)) ∧ generating a := by
  sorry

end OMA.S_oeis_a152120

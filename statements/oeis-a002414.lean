import Mathlib

/-!
# A002414: Octagonal pyramidal numbers: a(n) = n*(n+1)*(2*n-1)/2.

Source: https://oeis.org/A002414
Credit: @bIackr0se

The entry gives the generating function `x*(1+5*x)/(1-x)^4`, conjectured by Simon Plouffe in his
1992 dissertation.

Formalization notes:
* The sequence is defined by the formula in its name. It is computed in `ℚ`, where the division
  by 2 is exact; `n*(n+1)*(2*n-1)` is always even, so every value is an integer
  (data: 1, 9, 30, 70, 135, 231, ... from n = 1).
* The entry has offset 1. Index 0 is included here with the same formula, which gives
  `a(0) = 0`, so the ordinary generating function `Sum_{n >= 1} a(n) x^n` is the power series
  of `a`.
* The generating function is stated as an identity of formal power series over `ℚ` with the
  denominator cleared: `A * (1 - x)^4 = x * (1 + 5x)`, where `A` is the ordinary generating
  function of the sequence.
-/

namespace OMA.S_oeis_a002414

/-- The octagonal pyramidal numbers `a(n) = n (n + 1) (2n - 1) / 2`. -/
def a (n : ℕ) : ℚ := (n : ℚ) * (n + 1) * (2 * n - 1) / 2

/-- The ordinary generating function of `a` is `x (1 + 5x) / (1 - x)^4`. -/
theorem main :
    PowerSeries.mk a * (1 - PowerSeries.X) ^ 4 =
      (PowerSeries.X : PowerSeries ℚ) * (1 + 5 * PowerSeries.X) := by
  sorry

end OMA.S_oeis_a002414

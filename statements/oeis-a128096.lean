import Mathlib

/-!
# A128096: Number of steps that touch the x-axis in all peakless Motzkin paths of length n.

Source: https://oeis.org/A128096
Credit: @vivanpoddar

The sequence (offset 1) begins 1, 2, 5, 12, 27, 62, 144, 336, 790, ...
The entry gives the generating function
  4[1-z^2-sqrt((1+z+z^2)(1-3z+z^2))]/[1-z+z^2+sqrt((1+z+z^2)(1-3z+z^2))]^2
(see the entry). It is used here as the definition: a(n) is the coefficient of x^n of that series, where
the square root is the power series with constant term 1 (the binomial series (1 + X)^(1/2) evaluated
at the radicand minus 1). With R = x^4 - 2*x^3 - x^2 - 2*x + 1 the series is, in normalised form,
  (-x^5 + 2*x^4 - 3*x^3 + 2*x^2 - 5*x + 2 + (x^3 - x^2 + 3*x - 2)*sqrt(R)) / (2*x^4),
which is the expression used below (the division by x^4 is the shift of the index by 4).
Expanding it reproduces the data of the entry.

The conjecture (R. J. Mathar, Jun 17 2016) reads
  Conjecture: -2*(n+4)*(1088*n-4241)*a(n) +(6616*n^2-12361*n-59102)*a(n-1) +2*(-1176*n^2+6520*n-4985)*a(n-2) +(2088*n^2-6071*n+16522) *a(n-3) +2*(-3352*n^2+22882*n-35653)*a(n-4) +(2264*n-6277)*(n-6) *a(n-5)=0
It involves a(n-5) and the offset is 1, so it is stated for n >= 6.
-/

namespace OMA.S_oeis_a128096

open PowerSeries

/-- The radicand of the generating function. -/
noncomputable def R : PowerSeries ℚ := 1 - 2 * X - X ^ 2 - 2 * X ^ 3 + X ^ 4

/-- The square root of the radicand with constant term 1: (1 + X)^(1/2) evaluated at R - 1. -/
noncomputable def S : PowerSeries ℚ := (PowerSeries.binomialSeries ℚ (1 / 2 : ℚ)).subst (R - 1)

/-- A128096: the coefficient of x^n in the generating function of the entry. -/
noncomputable def a (n : ℕ) : ℚ :=
  coeff (n + 4)
    ((2 - 5 * X + 2 * X ^ 2 - 3 * X ^ 3 + 2 * X ^ 4 - X ^ 5 + (-2 + 3 * X - X ^ 2 + X ^ 3) * S)
      * (2 : PowerSeries ℚ)⁻¹)

/-- The conjectured recurrence for A128096. -/
theorem main : ∀ n : ℕ, 6 ≤ n →
    (-2176 * (n : ℚ) ^ 2 - 222 * (n : ℚ) + 33928) * a n
      + (6616 * (n : ℚ) ^ 2 - 12361 * (n : ℚ) - 59102) * a (n - 1)
      + (-2352 * (n : ℚ) ^ 2 + 13040 * (n : ℚ) - 9970) * a (n - 2)
      + (2088 * (n : ℚ) ^ 2 - 6071 * (n : ℚ) + 16522) * a (n - 3)
      + (-6704 * (n : ℚ) ^ 2 + 45764 * (n : ℚ) - 71306) * a (n - 4)
      + (2264 * (n : ℚ) ^ 2 - 19861 * (n : ℚ) + 37662) * a (n - 5) = 0 := by
  sorry

end OMA.S_oeis_a128096

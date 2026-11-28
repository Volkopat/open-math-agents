import Mathlib

/-!
# A226434: The number of sum decomposable permutations which avoid the patterns 3124 and 4312.

Source: https://oeis.org/A226434
Credit: @vivanpoddar

The sequence (offset 1) begins 0, 1, 3, 10, 37, 146, 595, 2456, 10167, ...
The entry gives the generating function
  -(8*x^5 - 16*x^4 + 19*x^3 - 8*x^2 - sqrt(-4*x + 1)*(2*x^4 + x^3 - 4*x^2 + x) + x)/(12*x^4 - 31*x^3 + 27*x^2 + sqrt(-4*x + 1)*(4*x^4 - 13*x^3 + 15*x^2 - 7*x + 1) - 9*x + 1)
(see the entry). It is used here as the definition: a(n) is the coefficient of x^n of that series, where
the square root is the power series with constant term 1 (the binomial series (1 + X)^(1/2) evaluated
at the radicand minus 1). With R = 1 - 4*x the series is, in normalised form,
  (8*x^5 - 25*x^4 + 46*x^3 - 34*x^2 + 10*x - 1 + (-4*x^5 + 9*x^4 - 18*x^3 + 20*x^2 - 8*x + 1)*sqrt(R)) / (-8*x^5 + 18*x^4 - 12*x^3 + 2*x^2),
which is the expression used below (the division by x^2 is the shift of the index by 2).
Expanding it reproduces the data of the entry.

The conjecture (R. J. Mathar, Jun 14 2016) reads
  Conjecture: +(95*n+537)*(n+2)*a(n) +(95*n^2-16421*n-14748) *a(n-1) +(-6403*n^2+124495*n-60066) *a(n-2) +(21565*n^2-354883*n+596496) *a(n-3) +2*(-5092*n^2+138877*n-395970)  *a(n-4) +8*(-2470*n^2+11113*n+12744) *a(n-5) +192*(38*n-67)*(2*n-13)*a(n-6)=0
It involves a(n-6) and the offset is 1, so it is stated for n >= 7.
-/

namespace OMA.S_oeis_a226434

open PowerSeries

/-- The radicand of the generating function. -/
noncomputable def R : PowerSeries ℚ := 1 - 4 * X

/-- The square root of the radicand with constant term 1: (1 + X)^(1/2) evaluated at R - 1. -/
noncomputable def S : PowerSeries ℚ := (PowerSeries.binomialSeries ℚ (1 / 2 : ℚ)).subst (R - 1)

/-- A226434: the coefficient of x^n in the generating function of the entry. -/
noncomputable def a (n : ℕ) : ℚ :=
  coeff (n + 2)
    ((-1 + 10 * X - 34 * X ^ 2 + 46 * X ^ 3 - 25 * X ^ 4 + 8 * X ^ 5 + (1 - 8 * X + 20 * X ^ 2 - 18 * X ^ 3 + 9 * X ^ 4 - 4 * X ^ 5) * S)
      * (2 - 12 * X + 18 * X ^ 2 - 8 * X ^ 3 : PowerSeries ℚ)⁻¹)

/-- The conjectured recurrence for A226434. -/
theorem main : ∀ n : ℕ, 7 ≤ n →
    (95 * (n : ℚ) ^ 2 + 727 * (n : ℚ) + 1074) * a n
      + (95 * (n : ℚ) ^ 2 - 16421 * (n : ℚ) - 14748) * a (n - 1)
      + (-6403 * (n : ℚ) ^ 2 + 124495 * (n : ℚ) - 60066) * a (n - 2)
      + (21565 * (n : ℚ) ^ 2 - 354883 * (n : ℚ) + 596496) * a (n - 3)
      + (-10184 * (n : ℚ) ^ 2 + 277754 * (n : ℚ) - 791940) * a (n - 4)
      + (-19760 * (n : ℚ) ^ 2 + 88904 * (n : ℚ) + 101952) * a (n - 5)
      + (14592 * (n : ℚ) ^ 2 - 120576 * (n : ℚ) + 167232) * a (n - 6) = 0 := by
  sorry

end OMA.S_oeis_a226434

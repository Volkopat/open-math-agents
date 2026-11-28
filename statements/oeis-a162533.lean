import Mathlib

/-!
# A162533: a(n) = Sum_{k=0..n} binomial(n,2k)*A002426(k).

Source: https://oeis.org/A162533
Credit: @vivanpoddar

The sequence (offset 0) begins 1, 1, 2, 4, 10, 26, 68, 176, 454, ...
The entry gives the generating function
  (1-x)/sqrt(1-4*x+4*x^2-4*x^4)
(Paul Barry, Oct 13 2009). It is used here as the definition: a(n) is the coefficient of x^n of that series, where
the square root is the power series with constant term 1 (the binomial series (1 + X)^(1/2) evaluated
at the radicand minus 1). With R = -4*x^4 + 4*x^2 - 4*x + 1 the series is, in normalised form,
  (0 + (1 - x)*sqrt(R)) / (-4*x^4 + 4*x^2 - 4*x + 1),
which is the expression used below (the division by x^0 is the shift of the index by 0).
Expanding it reproduces the data of the entry.

The conjecture (R. J. Mathar, Nov 16 2011) reads
  Conjecture: n*a(n) + (4-5*n)*a(n-1) + 2*(4*n-7)*a(n-2) + 4*(3-n)*a(n-3) + 4*(2-n)*a(n-4) + 4*(n-4)*a(n-5) = 0
It involves a(n-5) and the offset is 0, so it is stated for n >= 5.
-/

namespace OMA.S_oeis_a162533

open PowerSeries

/-- The radicand of the generating function. -/
noncomputable def R : PowerSeries ℚ := 1 - 4 * X + 4 * X ^ 2 - 4 * X ^ 4

/-- The square root of the radicand with constant term 1: (1 + X)^(1/2) evaluated at R - 1. -/
noncomputable def S : PowerSeries ℚ := (PowerSeries.binomialSeries ℚ (1 / 2 : ℚ)).subst (R - 1)

/-- A162533: the coefficient of x^n in the generating function of the entry. -/
noncomputable def a (n : ℕ) : ℚ :=
  coeff n
    (((1 - X) * S)
      * (1 - 4 * X + 4 * X ^ 2 - 4 * X ^ 4 : PowerSeries ℚ)⁻¹)

/-- The conjectured recurrence for A162533. -/
theorem main : ∀ n : ℕ, 5 ≤ n →
    (n : ℚ) * a n + (-5 * (n : ℚ) + 4) * a (n - 1) + (8 * (n : ℚ) - 14) * a (n - 2)
      + (-4 * (n : ℚ) + 12) * a (n - 3) + (-4 * (n : ℚ) + 8) * a (n - 4)
      + (4 * (n : ℚ) - 16) * a (n - 5) = 0 := by
  sorry

end OMA.S_oeis_a162533

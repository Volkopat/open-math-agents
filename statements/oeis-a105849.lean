import Mathlib

/-!
# A105849: Row sums of number triangle A105848.

Source: https://oeis.org/A105849
Credit: @vivanpoddar

The sequence (offset 0) begins 1, 3, 9, 28, 91, 308, 1079, 3888, 14332, ...
The entry gives the generating function
  (1-2x-sqrt((1-6x+8x^2-4x^3)/(1-2x)))/(2x^2)
(see the entry). It is used here as the definition: a(n) is the coefficient of x^n of that series, where
the square root is the power series with constant term 1 (the binomial series (1 + X)^(1/2) evaluated
at the radicand minus 1). With R = 8*x^4 - 20*x^3 + 20*x^2 - 8*x + 1 the series is, in normalised form,
  (4*x^2 - 4*x + 1 + (-1)*sqrt(R)) / (-4*x^3 + 2*x^2),
which is the expression used below (the division by x^2 is the shift of the index by 2).
Expanding it reproduces the data of the entry.

The conjecture (R. J. Mathar, Nov 16 2012) reads
  Conjecture: (n+2)*a(n) +2*(-4*n-3)*a(n-1) +4*(5*n-2)*a(n-2) +2*(-10*n+17)*a(n-3) +8*(n-3)*a(n-4)=0
It involves a(n-4) and the offset is 0, so it is stated for n >= 4.
-/

namespace OMA.S_oeis_a105849

open PowerSeries

/-- The radicand of the generating function. -/
noncomputable def R : PowerSeries ℚ := 1 - 8 * X + 20 * X ^ 2 - 20 * X ^ 3 + 8 * X ^ 4

/-- The square root of the radicand with constant term 1: (1 + X)^(1/2) evaluated at R - 1. -/
noncomputable def S : PowerSeries ℚ := (PowerSeries.binomialSeries ℚ (1 / 2 : ℚ)).subst (R - 1)

/-- A105849: the coefficient of x^n in the generating function of the entry. -/
noncomputable def a (n : ℕ) : ℚ :=
  coeff (n + 2)
    ((1 - 4 * X + 4 * X ^ 2 - S)
      * (2 - 4 * X : PowerSeries ℚ)⁻¹)

/-- The conjectured recurrence for A105849. -/
theorem main : ∀ n : ℕ, 4 ≤ n →
    ((n : ℚ) + 2) * a n + (-8 * (n : ℚ) - 6) * a (n - 1) + (20 * (n : ℚ) - 8) * a (n - 2)
      + (-20 * (n : ℚ) + 34) * a (n - 3) + (8 * (n : ℚ) - 24) * a (n - 4) = 0 := by
  sorry

end OMA.S_oeis_a105849

import Mathlib

/-!
# A191585: Central coefficients of the Riordan matrix (1/(1-3*x^2),x/(1-x)) (A191582).

Source: https://oeis.org/A191585
Credit: @vivanpoddar

The sequence (offset 0) begins 1, 1, 6, 19, 74, 276, 1056, 4047, 15606, ...
The entry gives the generating function
  (2-11*x+12*x^2+(2-9*x)*sqrt(1-4*x))/(2*(1-4*x)*(2-6*x-9*x^2))
(see the entry). It is used here as the definition: a(n) is the coefficient of x^n of that series, where
the square root is the power series with constant term 1 (the binomial series (1 + X)^(1/2) evaluated
at the radicand minus 1). With R = 1 - 4*x the series is, in normalised form,
  (12*x^2 - 11*x + 2 + (2 - 9*x)*sqrt(R)) / (72*x^3 + 30*x^2 - 28*x + 4),
which is the expression used below (the division by x^0 is the shift of the index by 0).
Expanding it reproduces the data of the entry.

The conjecture (R. J. Mathar, Jun 14 2016) reads
  Conjecture: 2*n*(n+3)*a(n) +2*(-7*n^2-19*n+24)*a(n-1) +3*(5*n^2+11*n-48)*a(n-2) +18*(n+4)*(2*n-3)*a(n-3)=0
It involves a(n-3) and the offset is 0, so it is stated for n >= 3.
-/

namespace OMA.S_oeis_a191585

open PowerSeries

/-- The radicand of the generating function. -/
noncomputable def R : PowerSeries ℚ := 1 - 4 * X

/-- The square root of the radicand with constant term 1: (1 + X)^(1/2) evaluated at R - 1. -/
noncomputable def S : PowerSeries ℚ := (PowerSeries.binomialSeries ℚ (1 / 2 : ℚ)).subst (R - 1)

/-- A191585: the coefficient of x^n in the generating function of the entry. -/
noncomputable def a (n : ℕ) : ℚ :=
  coeff n
    ((2 - 11 * X + 12 * X ^ 2 + (2 - 9 * X) * S)
      * (4 - 28 * X + 30 * X ^ 2 + 72 * X ^ 3 : PowerSeries ℚ)⁻¹)

/-- The conjectured recurrence for A191585. -/
theorem main : ∀ n : ℕ, 3 ≤ n →
    (2 * (n : ℚ) ^ 2 + 6 * (n : ℚ)) * a n + (-14 * (n : ℚ) ^ 2 - 38 * (n : ℚ) + 48) * a (n - 1)
      + (15 * (n : ℚ) ^ 2 + 33 * (n : ℚ) - 144) * a (n - 2)
      + (36 * (n : ℚ) ^ 2 + 90 * (n : ℚ) - 216) * a (n - 3) = 0 := by
  sorry

end OMA.S_oeis_a191585

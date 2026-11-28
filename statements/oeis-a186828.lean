import Mathlib

/-!
# A186828: Diagonal sums of number triangle A186826.

Source: https://oeis.org/A186828
Credit: @vivanpoddar

The sequence (offset 0) begins 1, 1, 4, 14, 57, 247, 1124, 5296, 25621, ...
The entry gives the generating function
  (1+x-3x^2+x^3-(1+x^2)*sqrt(1-6x+x^2))/(4x(1-x+x^2+x^3))
(see the entry). It is used here as the definition: a(n) is the coefficient of x^n of that series, where
the square root is the power series with constant term 1 (the binomial series (1 + X)^(1/2) evaluated
at the radicand minus 1). With R = x^2 - 6*x + 1 the series is, in normalised form,
  (x^3 - 3*x^2 + x + 1 + (-x^2 - 1)*sqrt(R)) / (4*x^4 + 4*x^3 - 4*x^2 + 4*x),
which is the expression used below (the division by x^1 is the shift of the index by 1).
Expanding it reproduces the data of the entry.

The conjecture (R. J. Mathar, Feb 13 2015) reads
  Conjecture: (n+1)*a(n) +(-7*n+2)*a(n-1) +(9*n-7)*a(n-2) +(-13*n+36)*a(n-3) +(3*n-35)*a(n-4) +(-5*n+28)*a(n-5) +(-5*n+21)*a(n-6) +(n-6)*a(n-7)=0
It involves a(n-7) and the offset is 0, so it is stated for n >= 7.
-/

namespace OMA.S_oeis_a186828

open PowerSeries

/-- The radicand of the generating function. -/
noncomputable def R : PowerSeries ℚ := 1 - 6 * X + X ^ 2

/-- The square root of the radicand with constant term 1: (1 + X)^(1/2) evaluated at R - 1. -/
noncomputable def S : PowerSeries ℚ := (PowerSeries.binomialSeries ℚ (1 / 2 : ℚ)).subst (R - 1)

/-- A186828: the coefficient of x^n in the generating function of the entry. -/
noncomputable def a (n : ℕ) : ℚ :=
  coeff (n + 1)
    ((1 + X - 3 * X ^ 2 + X ^ 3 + (-1 - X ^ 2) * S)
      * (4 - 4 * X + 4 * X ^ 2 + 4 * X ^ 3 : PowerSeries ℚ)⁻¹)

/-- The conjectured recurrence for A186828. -/
theorem main : ∀ n : ℕ, 7 ≤ n →
    ((n : ℚ) + 1) * a n + (-7 * (n : ℚ) + 2) * a (n - 1) + (9 * (n : ℚ) - 7) * a (n - 2)
      + (-13 * (n : ℚ) + 36) * a (n - 3) + (3 * (n : ℚ) - 35) * a (n - 4)
      + (-5 * (n : ℚ) + 28) * a (n - 5) + (-5 * (n : ℚ) + 21) * a (n - 6)
      + ((n : ℚ) - 6) * a (n - 7) = 0 := by
  sorry

end OMA.S_oeis_a186828

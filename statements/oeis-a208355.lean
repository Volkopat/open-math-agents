import Mathlib

/-!
# A208355: Right edge of the triangle in A208101.

Source: https://oeis.org/A208355
Credit: @vivanpoddar

The sequence (offset 0) begins 1, 1, 1, 2, 2, 5, 5, 14, 14, ...
The entry gives the generating function
  ((((1+z)*(1-sqrt(1-4*z^2)))/(2*z^2))-1)/z
(Robert A. Russell, Jan 28 2024). It is used here as the definition: a(n) is the coefficient of x^n of that series, where
the square root is the power series with constant term 1 (the binomial series (1 + X)^(1/2) evaluated
at the radicand minus 1). With R = 1 - 4*x^2 the series is, in normalised form,
  (-2*x^2 + x + 1 + (-x - 1)*sqrt(R)) / (2*x^3),
which is the expression used below (the division by x^3 is the shift of the index by 3).
Expanding it reproduces the data of the entry.

The conjecture (R. J. Mathar, Aug 04 2015) reads
  Conjecture: -(n+3)*(n-2)*a(n) - 4*a(n-1) + 4*(n-1)^2*a(n-2) = 0
It involves a(n-2) and the offset is 0, so it is stated for n >= 2.
-/

namespace OMA.S_oeis_a208355

open PowerSeries

/-- The radicand of the generating function. -/
noncomputable def R : PowerSeries ℚ := 1 - 4 * X ^ 2

/-- The square root of the radicand with constant term 1: (1 + X)^(1/2) evaluated at R - 1. -/
noncomputable def S : PowerSeries ℚ := (PowerSeries.binomialSeries ℚ (1 / 2 : ℚ)).subst (R - 1)

/-- A208355: the coefficient of x^n in the generating function of the entry. -/
noncomputable def a (n : ℕ) : ℚ :=
  coeff (n + 3)
    ((1 + X - 2 * X ^ 2 + (-1 - X) * S)
      * (2 : PowerSeries ℚ)⁻¹)

/-- The conjectured recurrence for A208355. -/
theorem main : ∀ n : ℕ, 2 ≤ n →
    (-(n : ℚ) ^ 2 - (n : ℚ) + 6) * a n + (-4) * a (n - 1)
      + (4 * (n : ℚ) ^ 2 - 8 * (n : ℚ) + 4) * a (n - 2) = 0 := by
  sorry

end OMA.S_oeis_a208355

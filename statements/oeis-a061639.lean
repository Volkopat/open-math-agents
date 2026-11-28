import Mathlib

/-!
# A061639: Number of planar planted trees with n non-root nodes and every 2-valent node isolated.

Source: https://oeis.org/A061639
Credit: @vivanpoddar

The sequence (offset 0) begins 0, 1, 1, 1, 4, 10, 28, 85, 262, ...
The entry gives the generating function
  (1+x+x^2-sqrt(1-2x-5x^2-6x^3-3x^4))/(2*(1+x+x^2))
(see the entry). It is used here as the definition: a(n) is the coefficient of x^n of that series, where
the square root is the power series with constant term 1 (the binomial series (1 + X)^(1/2) evaluated
at the radicand minus 1). With R = -3*x^4 - 6*x^3 - 5*x^2 - 2*x + 1 the series is, in normalised form,
  (x^2 + x + 1 + (-1)*sqrt(R)) / (2*x^2 + 2*x + 2),
which is the expression used below (the division by x^0 is the shift of the index by 0).
Expanding it reproduces the data of the entry.

The conjecture (R. J. Mathar, Nov 15 2011) reads
  Conjecture: n*a(n) +2*(2-n)*a(n-1) +(14-5*n)*a(n-2) +6*(3-n)*a(n-3) +3*(4-n)*a(n-4)=0
It involves a(n-4) and the offset is 0, so it is stated for n >= 4.
-/

namespace OMA.S_oeis_a061639

open PowerSeries

/-- The radicand of the generating function. -/
noncomputable def R : PowerSeries ℚ := 1 - 2 * X - 5 * X ^ 2 - 6 * X ^ 3 - 3 * X ^ 4

/-- The square root of the radicand with constant term 1: (1 + X)^(1/2) evaluated at R - 1. -/
noncomputable def S : PowerSeries ℚ := (PowerSeries.binomialSeries ℚ (1 / 2 : ℚ)).subst (R - 1)

/-- A061639: the coefficient of x^n in the generating function of the entry. -/
noncomputable def a (n : ℕ) : ℚ :=
  coeff n
    ((1 + X + X ^ 2 - S)
      * (2 + 2 * X + 2 * X ^ 2 : PowerSeries ℚ)⁻¹)

/-- The conjectured recurrence for A061639. -/
theorem main : ∀ n : ℕ, 4 ≤ n →
    (n : ℚ) * a n + (-2 * (n : ℚ) + 4) * a (n - 1) + (-5 * (n : ℚ) + 14) * a (n - 2)
      + (-6 * (n : ℚ) + 18) * a (n - 3) + (-3 * (n : ℚ) + 12) * a (n - 4) = 0 := by
  sorry

end OMA.S_oeis_a061639

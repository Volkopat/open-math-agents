import Mathlib

/-!
# A100098: An inverse Chebyshev transform of (1-x)/(1-2x).

Source: https://oeis.org/A100098
Credit: @vivanpoddar

The sequence (offset 0) begins 1, 1, 4, 7, 22, 46, 130, 295, 790, ...
The entry gives the generating function
  sqrt(1-4x^2)*(sqrt(1-4x^2)-6x+3)/(2*(2-5x)*(1-4x^2))
(see the entry). It is used here as the definition: a(n) is the coefficient of x^n of that series, where
the square root is the power series with constant term 1 (the binomial series (1 + X)^(1/2) evaluated
at the radicand minus 1). With R = 1 - 4*x^2 the series is, in normalised form,
  (2*x + 1 + (3)*sqrt(R)) / (-20*x^2 - 2*x + 4),
which is the expression used below (the division by x^0 is the shift of the index by 0).
Expanding it reproduces the data of the entry.

The conjecture (R. J. Mathar, Nov 22 2012) reads
  Conjecture: 2*n*a(n) + (-5*n+4)*a(n-1) + 2*(-4*n+3)*a(n-2) + 20*(n-2)*a(n-3) = 0
It involves a(n-3) and the offset is 0, so it is stated for n >= 3.
-/

namespace OMA.S_oeis_a100098

open PowerSeries

/-- The radicand of the generating function. -/
noncomputable def R : PowerSeries ℚ := 1 - 4 * X ^ 2

/-- The square root of the radicand with constant term 1: (1 + X)^(1/2) evaluated at R - 1. -/
noncomputable def S : PowerSeries ℚ := (PowerSeries.binomialSeries ℚ (1 / 2 : ℚ)).subst (R - 1)

/-- A100098: the coefficient of x^n in the generating function of the entry. -/
noncomputable def a (n : ℕ) : ℚ :=
  coeff n
    ((1 + 2 * X + (3) * S)
      * (4 - 2 * X - 20 * X ^ 2 : PowerSeries ℚ)⁻¹)

/-- The conjectured recurrence for A100098. -/
theorem main : ∀ n : ℕ, 3 ≤ n →
    (2 * (n : ℚ)) * a n + (-5 * (n : ℚ) + 4) * a (n - 1) + (-8 * (n : ℚ) + 6) * a (n - 2)
      + (20 * (n : ℚ) - 40) * a (n - 3) = 0 := by
  sorry

end OMA.S_oeis_a100098

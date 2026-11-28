import Mathlib

/-!
# A228180: The number of single edges on the boundary of ordered trees with n edges.

Source: https://oeis.org/A228180
Credit: @ivillar

Status: false as stated at n = 3 (a(0..3) = 0, 1, 2, 6 and the left side is 12 there); main is the corrected recurrence (n >= 4), which holds for the series as defined (a proof is filed with this statement).

The sequence (offset 0) begins 0, 1, 2, 6, 19, 61, 199, 661, 2234, ...
The entry gives the generating function
  (x*C+2*x^3*C^4)/(1-x) where C is the g.f. for the Catalan numbers A000108.
It is used here as the definition: a(n) is the coefficient of x^n of that series, where the square
root is the power series with constant term 1 (the binomial series (1 + X)^(1/2) evaluated at the
radicand minus 1), with R = 1-4*X the radicand. Substituting and rationalizing
(multiplying by conjugates under sqrt(R) -> -sqrt(R)) and clearing denominators, the series is
(G) / (C * x^2) with polynomials G (linear in sqrt(R)) and C, C of nonzero constant term; the
division by x^2 is the shift of the index by 2. Expanding it reproduces the data of the entry.

The conjecture (R. J. Mathar, Aug 25 2013) reads
  Conjecture: 2*(n+1)*a(n) +(-13*n+5)*a(n-1) +(23*n-37)*a(n-2) +6*(-2*n+5)*a(n-3)=0.
It involves a(n-3) and fails at n = 3, so the corrected recurrence is stated for n >= 4.
-/

namespace OMA.S_oeis_a228180

open PowerSeries

/-- The radicand of the generating function. -/
noncomputable def R : PowerSeries ℚ := 1 - 4 * X

/-- The square root of the radicand with constant term 1: (1 + X)^(1/2) evaluated at R - 1. -/
noncomputable def S : PowerSeries ℚ := (PowerSeries.binomialSeries ℚ (1 / 2 : ℚ)).subst (R - 1)

/-- A228180: the coefficient of x^n in the generating function of the entry. -/
noncomputable def a (n : ℕ) : ℚ :=
  coeff (n + 2)
    ((2 * X - 9 * X ^ 2 + 11 * X ^ 3 - 4 * X ^ 4 + (-2 * X + 5 * X ^ 2 - 3 * X ^ 3) * S)
      * (2 - 4 * X + 2 * X ^ 2 : PowerSeries ℚ)⁻¹)

/-- The corrected recurrence for A228180. -/
theorem main : ∀ n : ℕ, 4 ≤ n →
    (2 * (n : ℚ) + 2) * a n + (-13 * (n : ℚ) + 5) * a (n - 1) + (23 * (n : ℚ) - 37) * a (n - 2)
      + (-12 * (n : ℚ) + 30) * a (n - 3) = 0 := by
  sorry

end OMA.S_oeis_a228180

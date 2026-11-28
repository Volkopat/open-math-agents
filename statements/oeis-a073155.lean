import Mathlib

/-!
# A073155: Leftmost column sequence of triangle A073153.

Source: https://oeis.org/A073155
Credit: @ivillar

Status: open conjecture of the entry; it holds for the series as defined (a proof is filed with this statement).

The sequence (offset 0) begins 1, 1, 4, 14, 56, 237, 1046, 4762, 22198, ...
The entry gives the generating function
  1/2*(1-(1-4*x*(1+x)^2)^(1/2))/x/(1+x)^2.
It is used here as the definition: a(n) is the coefficient of x^n of that series, where the square
root is the power series with constant term 1 (the binomial series (1 + X)^(1/2) evaluated at the
radicand minus 1), with R = 1-4*X-8*X^2-4*X^3 the radicand. This is (1 - sqrt(R))/(2x(1+x)^2) with R = 1 - 4x(1+x)^2. Substituting and rationalizing
(multiplying by conjugates under sqrt(R) -> -sqrt(R)) and clearing denominators, the series is
(G) / (C * x^2) with polynomials G (linear in sqrt(R)) and C, C of nonzero constant term; the
division by x^2 is the shift of the index by 2. Expanding it reproduces the data of the entry.

The conjecture (R. J. Mathar, Nov 26 2012) reads
  Conjecture: (n+1)*a(n) + (-3*n+4)*a(n-1) + 2*(-6*n+7)*a(n-2) + 2*(-6*n+11)*a(n-3) + 2*(-2*n+5)*a(n-4)=0.
It involves a(n-4) and the offset is 0, so it is stated for n >= 4.
-/

namespace OMA.S_oeis_a073155

open PowerSeries

/-- The radicand of the generating function. -/
noncomputable def R : PowerSeries ℚ := 1 - 4 * X - 8 * X ^ 2 - 4 * X ^ 3

/-- The square root of the radicand with constant term 1: (1 + X)^(1/2) evaluated at R - 1. -/
noncomputable def S : PowerSeries ℚ := (PowerSeries.binomialSeries ℚ (1 / 2 : ℚ)).subst (R - 1)

/-- A073155: the coefficient of x^n in the generating function of the entry. -/
noncomputable def a (n : ℕ) : ℚ :=
  coeff (n + 2)
    ((X + 2 * X ^ 2 + X ^ 3 + (-X - 2 * X ^ 2 - X ^ 3) * S)
      * (2 + 8 * X + 12 * X ^ 2 + 8 * X ^ 3 + 2 * X ^ 4 : PowerSeries ℚ)⁻¹)

/-- The recurrence for A073155. -/
theorem main : ∀ n : ℕ, 4 ≤ n →
    ((n : ℚ) + 1) * a n + (-3 * (n : ℚ) + 4) * a (n - 1) + (-12 * (n : ℚ) + 14) * a (n - 2)
      + (-12 * (n : ℚ) + 22) * a (n - 3) + (-4 * (n : ℚ) + 10) * a (n - 4) = 0 := by
  sorry

end OMA.S_oeis_a073155

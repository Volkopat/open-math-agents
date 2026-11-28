import Mathlib

/-!
# A210064: Total number of 231 patterns in the set of permutations avoiding 123.

Source: https://oeis.org/A210064
Credit: @ivillar

Status: open conjecture of the entry; it holds for the series as defined (a proof is filed with this statement).

The sequence (offset 1) begins 0, 0, 1, 11, 81, 500, 2794, 14649, 73489, ...
The entry gives the generating function
  x/(2*(1-4*x)^2) + (x-1)/(2*(1-4*x)^(3/2)) + 1/(2 - 8*x).
It is used here as the definition: a(n) is the coefficient of x^n of that series, where the square
root is the power series with constant term 1 (the binomial series (1 + X)^(1/2) evaluated at the
radicand minus 1), with R = 1-4*X the radicand. Substituting and rationalizing
(multiplying by conjugates under sqrt(R) -> -sqrt(R)) and clearing denominators, the series is
(G) / (C * x^0) with polynomials G (linear in sqrt(R)) and C, C of nonzero constant term; the
division by x^0 is the shift of the index by 0. Expanding it reproduces the data of the entry.

The conjecture (R. J. Mathar, Oct 08 2016) reads
  Conjecture: n*(n-3)*a(n) +2*(-4*n^2+11*n-2)*a(n-1) +8*(n-1)*(2*n-3)*a(n-2)=0.
It involves a(n-2) and the offset is 1, so it is stated for n >= 3.
-/

namespace OMA.S_oeis_a210064

open PowerSeries

/-- The radicand of the generating function. -/
noncomputable def R : PowerSeries ℚ := 1 - 4 * X

/-- The square root of the radicand with constant term 1: (1 + X)^(1/2) evaluated at R - 1. -/
noncomputable def S : PowerSeries ℚ := (PowerSeries.binomialSeries ℚ (1 / 2 : ℚ)).subst (R - 1)

/-- A210064: the coefficient of x^n in the generating function of the entry. -/
noncomputable def a (n : ℕ) : ℚ :=
  coeff n
    ((1 - 11 * X + 40 * X ^ 2 - 48 * X ^ 3 + (-1 + 9 * X - 24 * X ^ 2 + 16 * X ^ 3) * S)
      * (2 - 32 * X + 192 * X ^ 2 - 512 * X ^ 3 + 512 * X ^ 4 : PowerSeries ℚ)⁻¹)

/-- The recurrence for A210064. -/
theorem main : ∀ n : ℕ, 3 ≤ n →
    ((n : ℚ) ^ 2 - 3 * (n : ℚ)) * a n + (-8 * (n : ℚ) ^ 2 + 22 * (n : ℚ) - 4) * a (n - 1)
      + (16 * (n : ℚ) ^ 2 - 40 * (n : ℚ) + 24) * a (n - 2) = 0 := by
  sorry

end OMA.S_oeis_a210064

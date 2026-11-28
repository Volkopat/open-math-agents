import Mathlib

/-!
# A119967: A transform of the central binomial coefficients C(n,floor(n/2)).

Source: https://oeis.org/A119967
Credit: @ivillar

Status: false as stated. With a(0..4) = 1, 1, 2, 4, 9 the left side at n = 4 is 54, not 0 (the recurrence fails at every n checked from 4 to 35); the statement is kept as the target of a disproof.

The sequence (offset 0) begins 1, 1, 2, 4, 9, 21, 49, 113, 259, ...
The entry gives the generating function
  2*(1-x)/(1-2*x-x^2+sqrt(1-4*x+6*x^2-4*x^3-3*x^4)).
It is used here as the definition: a(n) is the coefficient of x^n of that series, where the square
root is the power series with constant term 1 (the binomial series (1 + X)^(1/2) evaluated at the
radicand minus 1), with R = 1-4*X+6*X^2-4*X^3-3*X^4 the radicand. Substituting and rationalizing
(multiplying by conjugates under sqrt(R) -> -sqrt(R)) and clearing denominators, the series is
(G) / (C * x^4) with polynomials G (linear in sqrt(R)) and C, C of nonzero constant term; the
division by x^4 is the shift of the index by 4. Expanding it reproduces the data of the entry.

The conjecture (R. J. Mathar, Nov 14 2011) reads
  Conjecture: (n+2)*(n-3)*a(n) +(2+2*n-n^2)*a(n-1) +(3*n-5)*(n-2)*a(n-2) -(n-2)*(n-3)*a(n-3) -(n-2)*(n-3)*a(n-4)=0.
It involves a(n-4) and the offset is 0, so it is stated for n >= 4.
-/

namespace OMA.S_oeis_a119967

open PowerSeries

/-- The radicand of the generating function. -/
noncomputable def R : PowerSeries ℚ := 1 - 4 * X + 6 * X ^ 2 - 4 * X ^ 3 - 3 * X ^ 4

/-- The square root of the radicand with constant term 1: (1 + X)^(1/2) evaluated at R - 1. -/
noncomputable def S : PowerSeries ℚ := (PowerSeries.binomialSeries ℚ (1 / 2 : ℚ)).subst (R - 1)

/-- A119967: the coefficient of x^n in the generating function of the entry. -/
noncomputable def a (n : ℕ) : ℚ :=
  coeff (n + 4)
    ((-X ^ 2 + 3 * X ^ 3 - X ^ 4 - X ^ 5 + (X ^ 2 - X ^ 3) * S)
      * (2 - 4 * X - 2 * X ^ 2 : PowerSeries ℚ)⁻¹)

/-- The recurrence for A119967. -/
theorem main : ∀ n : ℕ, 4 ≤ n →
    ((n : ℚ) ^ 2 - (n : ℚ) - 6) * a n + (-(n : ℚ) ^ 2 + 2 * (n : ℚ) + 2) * a (n - 1)
      + (3 * (n : ℚ) ^ 2 - 11 * (n : ℚ) + 10) * a (n - 2)
      + (-(n : ℚ) ^ 2 + 5 * (n : ℚ) - 6) * a (n - 3)
      + (-(n : ℚ) ^ 2 + 5 * (n : ℚ) - 6) * a (n - 4) = 0 := by
  sorry

end OMA.S_oeis_a119967

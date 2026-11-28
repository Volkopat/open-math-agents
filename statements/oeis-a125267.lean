import Mathlib

/-!
# A125267: Number of Motzkin paths with no peaks and with level steps at height 0 having three colors except that consecutive level steps at height 0 must have different colors.

Source: https://oeis.org/A125267
Credit: @ivillar

Status: open conjecture of the entry; it holds for the series as defined (a proof is filed with this statement).

The sequence (offset 0) begins 1, 3, 6, 13, 30, 71, 171, 417, 1026, ...
The entry gives the generating function
  (g(x)*(1+x))/(1-x*g(x)) where g(x)=((1-x+x^2)-sqrt((1-x+x^2)^2-4x^2))/(2*x^2).
It is used here as the definition: a(n) is the coefficient of x^n of that series, where the square
root is the power series with constant term 1 (the binomial series (1 + X)^(1/2) evaluated at the
radicand minus 1), with R = 1-2*X-X^2-2*X^3+X^4 the radicand. Substituting and rationalizing
(multiplying by conjugates under sqrt(R) -> -sqrt(R)) and clearing denominators, the series is
(G) / (C * x^2) with polynomials G (linear in sqrt(R)) and C, C of nonzero constant term; the
division by x^2 is the shift of the index by 2. Expanding it reproduces the data of the entry.

The conjecture (R. J. Mathar, Jun 17 2016) reads
  Conjecture: -(n+1)*(n-2)*a(n) +2*(n^2-n-3)*a(n-1) +(n^2-3*n+8)*a(n-2) +2*(n^2-5*n+3)*a(n-3) -(n-1)*(n-4)*a(n-4)=0.
It involves a(n-4) and the offset is 0, so it is stated for n >= 4.
-/

namespace OMA.S_oeis_a125267

open PowerSeries

/-- The radicand of the generating function. -/
noncomputable def R : PowerSeries ℚ := 1 - 2 * X - X ^ 2 - 2 * X ^ 3 + X ^ 4

/-- The square root of the radicand with constant term 1: (1 + X)^(1/2) evaluated at R - 1. -/
noncomputable def S : PowerSeries ℚ := (PowerSeries.binomialSeries ℚ (1 / 2 : ℚ)).subst (R - 1)

/-- A125267: the coefficient of x^n in the generating function of the entry. -/
noncomputable def a (n : ℕ) : ℚ :=
  coeff (n + 2)
    ((-X + 2 * X ^ 2 + 2 * X ^ 3 - X ^ 4 + (X + X ^ 2) * S)
      * (2 - 6 * X + 2 * X ^ 2 : PowerSeries ℚ)⁻¹)

/-- The recurrence for A125267. -/
theorem main : ∀ n : ℕ, 4 ≤ n →
    (-(n : ℚ) ^ 2 + (n : ℚ) + 2) * a n + (2 * (n : ℚ) ^ 2 - 2 * (n : ℚ) - 6) * a (n - 1)
      + ((n : ℚ) ^ 2 - 3 * (n : ℚ) + 8) * a (n - 2)
      + (2 * (n : ℚ) ^ 2 - 10 * (n : ℚ) + 6) * a (n - 3)
      + (-(n : ℚ) ^ 2 + 5 * (n : ℚ) - 4) * a (n - 4) = 0 := by
  sorry

end OMA.S_oeis_a125267

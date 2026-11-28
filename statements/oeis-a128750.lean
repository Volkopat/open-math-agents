import Mathlib

/-!
# A128750: Number of skew Dyck paths of semilength n having no ascents of length 1.

Source: https://oeis.org/A128750
Credit: @ivillar

Status: open conjecture of the entry; it holds for the series as defined (a proof is filed with this statement).

The sequence (offset 0) begins 1, 0, 2, 4, 14, 44, 150, 520, 1850, ...
The entry gives the generating function
  G = G(z) satisfies z(1 + z)G^2 - (1 - z^2)G + 1 - z = 0.
It is used here as the definition: a(n) is the coefficient of x^n of that series, where the square
root is the power series with constant term 1 (the binomial series (1 + X)^(1/2) evaluated at the
radicand minus 1), with R = 1-4*X-2*X^2+4*X^3+X^4 the radicand. The power series solution G with G(0) = 1 of that quadratic equation is G = ((1 - z^2) - sqrt(R))/(2z(1+z)), with R = (1 - z^2)^2 - 4z(1+z)(1-z). Substituting and rationalizing
(multiplying by conjugates under sqrt(R) -> -sqrt(R)) and clearing denominators, the series is
(G) / (C * x^2) with polynomials G (linear in sqrt(R)) and C, C of nonzero constant term; the
division by x^2 is the shift of the index by 2. Expanding it reproduces the data of the entry.

The conjecture (R. J. Mathar, Nov 15 2012) reads
  Conjecture: (n+1)*a(n) +(-4*n+3)*a(n-1) +(-2*n-1)*a(n-2) +(4*n-11)*a(n-3) +(n-4)*a(n-4)=0.
It involves a(n-4) and the offset is 0, so it is stated for n >= 4.
-/

namespace OMA.S_oeis_a128750

open PowerSeries

/-- The radicand of the generating function. -/
noncomputable def R : PowerSeries ℚ := 1 - 4 * X - 2 * X ^ 2 + 4 * X ^ 3 + X ^ 4

/-- The square root of the radicand with constant term 1: (1 + X)^(1/2) evaluated at R - 1. -/
noncomputable def S : PowerSeries ℚ := (PowerSeries.binomialSeries ℚ (1 / 2 : ℚ)).subst (R - 1)

/-- A128750: the coefficient of x^n in the generating function of the entry. -/
noncomputable def a (n : ℕ) : ℚ :=
  coeff (n + 2)
    ((X - X ^ 3 + (-X) * S)
      * (2 + 2 * X : PowerSeries ℚ)⁻¹)

/-- The recurrence for A128750. -/
theorem main : ∀ n : ℕ, 4 ≤ n →
    ((n : ℚ) + 1) * a n + (-4 * (n : ℚ) + 3) * a (n - 1) + (-2 * (n : ℚ) - 1) * a (n - 2)
      + (4 * (n : ℚ) - 11) * a (n - 3) + ((n : ℚ) - 4) * a (n - 4) = 0 := by
  sorry

end OMA.S_oeis_a128750

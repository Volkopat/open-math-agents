import Mathlib

/-!
# A026571: a(n) = T(n,n-2), T given by A026568. Also a(n) = number of integer strings s(0), ..., s(n) counted by T, such that s(n) = 2.

Source: https://oeis.org/A026571
Credit: @ivillar

Status: open conjecture of the entry; it holds for the series as defined (a proof is filed with this statement).

The sequence (offset 2) begins 1, 2, 7, 16, 44, 106, 273, 672, 1696, ...
The entry gives the generating function
  (2*x^2+x-1+(1-x)*p(x))/(2*(x^3-x^2)*p(x)) with p(x) = sqrt((1-x-4*x^2)/(1-x)).
It is used here as the definition: a(n) is the coefficient of x^n of that series, where the square
root is the power series with constant term 1 (the binomial series (1 + X)^(1/2) evaluated at the
radicand minus 1), with R = 1-2*X-3*X^2+4*X^3 the radicand. Here p(x) = sqrt(R)/(1 - x) with R = (1 - x - 4x^2)(1 - x), both square roots having constant term 1. Substituting and rationalizing
(multiplying by conjugates under sqrt(R) -> -sqrt(R)) and clearing denominators, the series is
(G) / (C * x^4) with polynomials G (linear in sqrt(R)) and C, C of nonzero constant term; the
division by x^4 is the shift of the index by 4. Expanding it reproduces the data of the entry.

The conjecture (R. J. Mathar, Jun 23 2013) reads
  Conjecture: (n+2)*a(n) + 3*(-n-1)*a(n-1) - 3*n*a(n-2) + 11*(n-1)*a(n-3) + 2*(n-6)*a(n-4) + 4*(-2*n+7)*a(n-5) = 0.
It involves a(n-5) and the offset is 2, so it is stated for n >= 7.
-/

namespace OMA.S_oeis_a026571

open PowerSeries

/-- The radicand of the generating function. -/
noncomputable def R : PowerSeries ℚ := 1 - 2 * X - 3 * X ^ 2 + 4 * X ^ 3

/-- The square root of the radicand with constant term 1: (1 + X)^(1/2) evaluated at R - 1. -/
noncomputable def S : PowerSeries ℚ := (PowerSeries.binomialSeries ℚ (1 / 2 : ℚ)).subst (R - 1)

/-- A026571: the coefficient of x^n in the generating function of the entry. -/
noncomputable def a (n : ℕ) : ℚ :=
  coeff (n + 4)
    ((-X ^ 2 + 2 * X ^ 3 + 3 * X ^ 4 - 4 * X ^ 5 + (X ^ 2 - X ^ 3 - 2 * X ^ 4) * S)
      * (2 - 4 * X - 6 * X ^ 2 + 8 * X ^ 3 : PowerSeries ℚ)⁻¹)

/-- The recurrence for A026571. -/
theorem main : ∀ n : ℕ, 7 ≤ n →
    ((n : ℚ) + 2) * a n + (-3 * (n : ℚ) - 3) * a (n - 1) + (-3 * (n : ℚ)) * a (n - 2)
      + (11 * (n : ℚ) - 11) * a (n - 3) + (2 * (n : ℚ) - 12) * a (n - 4)
      + (-8 * (n : ℚ) + 28) * a (n - 5) = 0 := by
  sorry

end OMA.S_oeis_a026571

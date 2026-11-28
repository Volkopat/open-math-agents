import Mathlib

/-!
# A159769: Number of n-leaf binary trees that do not contain (((()())())(()(()()))) as a subtree.

Source: https://oeis.org/A159769
Credit: @ivillar

Status: open conjecture of the entry; it holds for the series as defined (a proof is filed with this statement).

The sequence (offset 1) begins 1, 1, 2, 5, 14, 41, 124, 384, 1212, ...
The entry gives the generating function
  f(x) satisfies (x-2) x f(x)^2 + (2 x^2 - 2 x + 1) f(x) + (x-1) x = 0.
It is used here as the definition: a(n) is the coefficient of x^n of that series, where the square
root is the power series with constant term 1 (the binomial series (1 + X)^(1/2) evaluated at the
radicand minus 1), with R = 1-4*X+4*X^3 the radicand. The power series solution f with f(0) = 0 of that quadratic equation is f = (sqrt(R) - (2x^2-2x+1))/(2(x-2)x), with R the discriminant (2x^2-2x+1)^2 - 4(x-2)x(x-1)x. Substituting and rationalizing
(multiplying by conjugates under sqrt(R) -> -sqrt(R)) and clearing denominators, the series is
(G) / (C * x^2) with polynomials G (linear in sqrt(R)) and C, C of nonzero constant term; the
division by x^2 is the shift of the index by 2. Expanding it reproduces the data of the entry.

The conjecture (R. J. Mathar, May 30 2014) reads
  Conjecture: 2*(n+1)*a(n) +3*(-3*n+1)*a(n-1) +2*(2*n-1)*a(n-2) +4*(2*n-7)*a(n-3) +2*(-2*n+7)*a(n-4)=0.
It involves a(n-4) and the offset is 1, so it is stated for n >= 5.
-/

namespace OMA.S_oeis_a159769

open PowerSeries

/-- The radicand of the generating function. -/
noncomputable def R : PowerSeries ℚ := 1 - 4 * X + 4 * X ^ 3

/-- The square root of the radicand with constant term 1: (1 + X)^(1/2) evaluated at R - 1. -/
noncomputable def S : PowerSeries ℚ := (PowerSeries.binomialSeries ℚ (1 / 2 : ℚ)).subst (R - 1)

/-- A159769: the coefficient of x^n in the generating function of the entry. -/
noncomputable def a (n : ℕ) : ℚ :=
  coeff (n + 2)
    ((2 * X - 5 * X ^ 2 + 6 * X ^ 3 - 2 * X ^ 4 + (-2 * X + X ^ 2) * S)
      * (8 - 8 * X + 2 * X ^ 2 : PowerSeries ℚ)⁻¹)

/-- The recurrence for A159769. -/
theorem main : ∀ n : ℕ, 5 ≤ n →
    (2 * (n : ℚ) + 2) * a n + (-9 * (n : ℚ) + 3) * a (n - 1) + (4 * (n : ℚ) - 2) * a (n - 2)
      + (8 * (n : ℚ) - 28) * a (n - 3) + (-4 * (n : ℚ) + 14) * a (n - 4) = 0 := by
  sorry

end OMA.S_oeis_a159769

import Mathlib

/-!
# A105524: Diagonal sums of number triangle A105522.

Source: https://oeis.org/A105524
Credit: @ivillar

Status: open conjecture of the entry; it holds for the series as defined (a proof is filed with this statement).

The sequence (offset 0) begins 1, -2, 2, 0, -1, -2, 4, 4, -10, ...
The entry gives the generating function
  ((1+2*x)*sqrt(1+4*x^2)-4*x^2-2*x-1)/(x^2*(sqrt(1+4*x^2)-3)).
It is used here as the definition: a(n) is the coefficient of x^n of that series, where the square
root is the power series with constant term 1 (the binomial series (1 + X)^(1/2) evaluated at the
radicand minus 1), with R = 1+4*X^2 the radicand. Substituting and rationalizing
(multiplying by conjugates under sqrt(R) -> -sqrt(R)) and clearing denominators, the series is
(G) / (C * x^4) with polynomials G (linear in sqrt(R)) and C, C of nonzero constant term; the
division by x^4 is the shift of the index by 4. Expanding it reproduces the data of the entry.

The conjecture (R. J. Mathar, Nov 09 2012) reads
  Conjecture: 2*(n+2)*(13*n^2-35*n+6)*a(n) +24*(n-8)*a(n-1) +(91*n^3-375*n^2+152*n+372)*a(n-2) +12*(8-n)*a(n-3) -4*(n-3)*(13*n^2-9*n-16)*a(n-4) = 0.
It involves a(n-4) and the offset is 0, so it is stated for n >= 4.
-/

namespace OMA.S_oeis_a105524

open PowerSeries

/-- The radicand of the generating function. -/
noncomputable def R : PowerSeries ℚ := 1 + 4 * X ^ 2

/-- The square root of the radicand with constant term 1: (1 + X)^(1/2) evaluated at R - 1. -/
noncomputable def S : PowerSeries ℚ := (PowerSeries.binomialSeries ℚ (1 / 2 : ℚ)).subst (R - 1)

/-- A105524: the coefficient of x^n in the generating function of the entry. -/
noncomputable def a (n : ℕ) : ℚ :=
  coeff (n + 4)
    ((2 * X ^ 2 + 4 * X ^ 3 + 7 * X ^ 4 - 10 * X ^ 5 - 4 * X ^ 6 + 4 * X ^ 7 + (-2 * X ^ 2 - 4 * X ^ 3 + 5 * X ^ 4 + 2 * X ^ 5 - 2 * X ^ 6) * S)
      * (8 - 8 * X ^ 2 + 2 * X ^ 4 : PowerSeries ℚ)⁻¹)

/-- The recurrence for A105524. -/
theorem main : ∀ n : ℕ, 4 ≤ n →
    (26 * (n : ℚ) ^ 3 - 18 * (n : ℚ) ^ 2 - 128 * (n : ℚ) + 24) * a n
      + (24 * (n : ℚ) - 192) * a (n - 1)
      + (91 * (n : ℚ) ^ 3 - 375 * (n : ℚ) ^ 2 + 152 * (n : ℚ) + 372) * a (n - 2)
      + (-12 * (n : ℚ) + 96) * a (n - 3)
      + (-52 * (n : ℚ) ^ 3 + 192 * (n : ℚ) ^ 2 - 44 * (n : ℚ) - 192) * a (n - 4) = 0 := by
  sorry

end OMA.S_oeis_a105524

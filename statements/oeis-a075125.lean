import Mathlib

/-!
# A075125: Number of parallelogram polyominoes of site-perimeter n (also called staircase polyominoes, although that term is overused).

Source: https://oeis.org/A075125
Credit: @ivillar

Status: open conjecture of the entry; it holds for the series as defined (a proof is filed with this statement).

The sequence (offset 1) begins 0, 0, 0, 1, 0, 2, 2, 5, 10, ...
The entry gives the generating function
  p^2/2*(1-p^2-2*p^3+p^4-(1+p-p^2)*sqrt((1+p+p^2)*(1-3*p+p^2)));
It is used here as the definition: a(n) is the coefficient of x^n of that series, where the square
root is the power series with constant term 1 (the binomial series (1 + X)^(1/2) evaluated at the
radicand minus 1), with R = 1-2*X-X^2-2*X^3+X^4 the radicand. Substituting and rationalizing
(multiplying by conjugates under sqrt(R) -> -sqrt(R)) and clearing denominators, the series is
(G) / (C * x^0) with polynomials G (linear in sqrt(R)) and C, C of nonzero constant term; the
division by x^0 is the shift of the index by 0. Expanding it reproduces the data of the entry.

The conjecture (R. J. Mathar, May 30 2016) reads
  Conjecture: -(2*n-11)*(n-2)*(2*n-9)*a(n) +4*(2*n-11)*(n-3)*(n-5)*a(n-1) +(4*n^3-60*n^2+317*n-582)*a(n-2) +2*(2*n-7)*(2*n^2-26*n+81)*a(n-3) -(n-10)*(2*n-7)*(2*n-9)*a(n-4)=0.
It involves a(n-4) and the offset is 1, so it is stated for n >= 5.
-/

namespace OMA.S_oeis_a075125

open PowerSeries

/-- The radicand of the generating function. -/
noncomputable def R : PowerSeries ℚ := 1 - 2 * X - X ^ 2 - 2 * X ^ 3 + X ^ 4

/-- The square root of the radicand with constant term 1: (1 + X)^(1/2) evaluated at R - 1. -/
noncomputable def S : PowerSeries ℚ := (PowerSeries.binomialSeries ℚ (1 / 2 : ℚ)).subst (R - 1)

/-- A075125: the coefficient of x^n in the generating function of the entry. -/
noncomputable def a (n : ℕ) : ℚ :=
  coeff n
    ((X ^ 2 - X ^ 4 - 2 * X ^ 5 + X ^ 6 + (-X ^ 2 - X ^ 3 + X ^ 4) * S)
      * (2 : PowerSeries ℚ)⁻¹)

/-- The recurrence for A075125. -/
theorem main : ∀ n : ℕ, 5 ≤ n →
    (-4 * (n : ℚ) ^ 3 + 48 * (n : ℚ) ^ 2 - 179 * (n : ℚ) + 198) * a n
      + (8 * (n : ℚ) ^ 3 - 108 * (n : ℚ) ^ 2 + 472 * (n : ℚ) - 660) * a (n - 1)
      + (4 * (n : ℚ) ^ 3 - 60 * (n : ℚ) ^ 2 + 317 * (n : ℚ) - 582) * a (n - 2)
      + (8 * (n : ℚ) ^ 3 - 132 * (n : ℚ) ^ 2 + 688 * (n : ℚ) - 1134) * a (n - 3)
      + (-4 * (n : ℚ) ^ 3 + 72 * (n : ℚ) ^ 2 - 383 * (n : ℚ) + 630) * a (n - 4) = 0 := by
  sorry

end OMA.S_oeis_a075125

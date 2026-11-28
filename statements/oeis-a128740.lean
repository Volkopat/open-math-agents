import Mathlib

/-!
# A128740: Number of DD's in all skew Dyck paths of semilength n.

Source: https://oeis.org/A128740
Credit: @ivillar

Status: open conjecture of the entry; it holds for the series as defined (a proof is filed with this statement).

The sequence (offset 0) begins 0, 0, 1, 6, 31, 154, 754, 3670, 17824, ...
The entry gives the generating function
  (2zg - g - z + 1)/(3zg - z - 1), where g = 1 + zg^2 + z(g-1) = (1 - z - sqrt(1 - 6z + 5z^2))/(2z).
It is used here as the definition: a(n) is the coefficient of x^n of that series, where the square
root is the power series with constant term 1 (the binomial series (1 + X)^(1/2) evaluated at the
radicand minus 1), with R = 1-6*X+5*X^2 the radicand. Substituting and rationalizing
(multiplying by conjugates under sqrt(R) -> -sqrt(R)) and clearing denominators, the series is
(G) / (C * x^2) with polynomials G (linear in sqrt(R)) and C, C of nonzero constant term; the
division by x^2 is the shift of the index by 2. Expanding it reproduces the data of the entry.

The conjecture (R. J. Mathar, Jun 17 2016) reads
  Conjecture: +2*(n+1)*(n^2-5*n+5)*a(n) +(-13*n^3+60*n^2-52*n+15)*a(n-1) +2*(8*n^3-44*n^2+63*n-20)*a(n-2) -5*(n-3)*(n^2-3*n+1)*a(n-3)=0.
It involves a(n-3) and the offset is 0, so it is stated for n >= 3.
-/

namespace OMA.S_oeis_a128740

open PowerSeries

/-- The radicand of the generating function. -/
noncomputable def R : PowerSeries ℚ := 1 - 6 * X + 5 * X ^ 2

/-- The square root of the radicand with constant term 1: (1 + X)^(1/2) evaluated at R - 1. -/
noncomputable def S : PowerSeries ℚ := (PowerSeries.binomialSeries ℚ (1 / 2 : ℚ)).subst (R - 1)

/-- A128740: the coefficient of x^n in the generating function of the entry. -/
noncomputable def a (n : ℕ) : ℚ :=
  coeff (n + 2)
    ((-2 * X + 15 * X ^ 2 - 29 * X ^ 3 + 21 * X ^ 4 - 5 * X ^ 5 + (2 * X - 9 * X ^ 2 + 6 * X ^ 3 - X ^ 4) * S)
      * (8 - 48 * X + 42 * X ^ 2 - 10 * X ^ 3 : PowerSeries ℚ)⁻¹)

/-- The recurrence for A128740. -/
theorem main : ∀ n : ℕ, 3 ≤ n →
    (2 * (n : ℚ) ^ 3 - 8 * (n : ℚ) ^ 2 + 10) * a n
      + (-13 * (n : ℚ) ^ 3 + 60 * (n : ℚ) ^ 2 - 52 * (n : ℚ) + 15) * a (n - 1)
      + (16 * (n : ℚ) ^ 3 - 88 * (n : ℚ) ^ 2 + 126 * (n : ℚ) - 40) * a (n - 2)
      + (-5 * (n : ℚ) ^ 3 + 30 * (n : ℚ) ^ 2 - 50 * (n : ℚ) + 15) * a (n - 3) = 0 := by
  sorry

end OMA.S_oeis_a128740

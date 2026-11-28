import Mathlib

/-!
# A128652: Number of square permutations of length n.

Source: https://oeis.org/A128652
Credit: @ivillar

Status: false as stated at n = 3 (a(0..3) = 0, 1, 2, 6 and the left side is 20 there); main is the corrected recurrence (n >= 4), which holds for the series as defined (a proof is filed with this statement).

The sequence (offset 1) begins 1, 2, 6, 24, 104, 464, 2088, 9392, 42064, ...
The entry gives the generating function
  x*(1-6*x+10*x^2-4*x^2*sqrt(1-4*x))/(1-4*x)^2 (See theorem 3.1 in Albert et al. reference).
It is used here as the definition: a(n) is the coefficient of x^n of that series, where the square
root is the power series with constant term 1 (the binomial series (1 + X)^(1/2) evaluated at the
radicand minus 1), with R = 1-4*X the radicand. Substituting and rationalizing
(multiplying by conjugates under sqrt(R) -> -sqrt(R)) and clearing denominators, the series is
(G) / (C * x^0) with polynomials G (linear in sqrt(R)) and C, C of nonzero constant term; the
division by x^0 is the shift of the index by 0. Expanding it reproduces the data of the entry.

The conjecture (R. J. Mathar, Oct 16 2017) reads
  Conjecture: +(n-3)*(n-8)*a(n) +2*(-4*n^2+43*n-96)*a(n-1) +8*(2*n-7)*(n-7)*a(n-2)=0.
It involves a(n-2) and fails at n = 3, so the corrected recurrence is stated for n >= 4.
-/

namespace OMA.S_oeis_a128652

open PowerSeries

/-- The radicand of the generating function. -/
noncomputable def R : PowerSeries ℚ := 1 - 4 * X

/-- The square root of the radicand with constant term 1: (1 + X)^(1/2) evaluated at R - 1. -/
noncomputable def S : PowerSeries ℚ := (PowerSeries.binomialSeries ℚ (1 / 2 : ℚ)).subst (R - 1)

/-- A128652: the coefficient of x^n in the generating function of the entry. -/
noncomputable def a (n : ℕ) : ℚ :=
  coeff n
    ((X - 14 * X ^ 2 + 74 * X ^ 3 - 176 * X ^ 4 + 160 * X ^ 5 + (-4 * X ^ 3 + 32 * X ^ 4 - 64 * X ^ 5) * S)
      * (1 - 16 * X + 96 * X ^ 2 - 256 * X ^ 3 + 256 * X ^ 4 : PowerSeries ℚ)⁻¹)

/-- The corrected recurrence for A128652. -/
theorem main : ∀ n : ℕ, 4 ≤ n →
    ((n : ℚ) ^ 2 - 11 * (n : ℚ) + 24) * a n + (-8 * (n : ℚ) ^ 2 + 86 * (n : ℚ) - 192) * a (n - 1)
      + (16 * (n : ℚ) ^ 2 - 168 * (n : ℚ) + 392) * a (n - 2) = 0 := by
  sorry

end OMA.S_oeis_a128652

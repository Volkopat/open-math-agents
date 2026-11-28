import Mathlib

/-!
# A174195: Number of permutations of 1..n that almost avoid 231.

Source: https://oeis.org/A174195
Credit: @ivillar

Status: false as stated: with a(0..3) = 1, 1, 2, 6 the left side is 13998 at n = 2 and 57576 at n = 3;
main is the corrected recurrence (n >= 4), which holds for the series as defined (a proof is filed with this statement).

The sequence (offset 0) begins 1, 1, 2, 6, 24, 111, 531, 2519, 11726, ...
The entry gives the generating function
  (1-5*x-6*x^2 + 45*x^3-24*x^4-(1 + x-4*x^2 + x^3)*(1-4*x)^(3/2))/(-2*x^2*(1-4*x)^(3/2)).
It is used here as the definition: a(n) is the coefficient of x^n of that series, where the square
root is the power series with constant term 1 (the binomial series (1 + X)^(1/2) evaluated at the
radicand minus 1), with R = 1-4*X the radicand. Substituting and rationalizing
(multiplying by conjugates under sqrt(R) -> -sqrt(R)) and clearing denominators, the series is
(G) / (C * x^4) with polynomials G (linear in sqrt(R)) and C, C of nonzero constant term; the
division by x^4 is the shift of the index by 4. Expanding it reproduces the data of the entry.

The conjecture (R. J. Mathar, Jun 14 2016) reads
  Conjecture: 2*(n+2)*(2013*n^2-10435*n+41550)*a(n) +(4026*n^3 -128025*n^2 +34955*n+59010)*a(n-1) -2 *(2*n-5)*(20130*n^2 -110855*n +93819) *a(n-2)=0.
It involves a(n-2) and fails at n = 3, so the corrected recurrence is stated for n >= 4.
-/

namespace OMA.S_oeis_a174195

open PowerSeries

/-- The radicand of the generating function. -/
noncomputable def R : PowerSeries ℚ := 1 - 4 * X

/-- The square root of the radicand with constant term 1: (1 + X)^(1/2) evaluated at R - 1. -/
noncomputable def S : PowerSeries ℚ := (PowerSeries.binomialSeries ℚ (1 / 2 : ℚ)).subst (R - 1)

/-- A174195: the coefficient of x^n in the generating function of the entry. -/
noncomputable def a (n : ℕ) : ℚ :=
  coeff (n + 4)
    ((X ^ 2 - 7 * X ^ 3 + 4 * X ^ 4 + 49 * X ^ 5 - 72 * X ^ 6 + 16 * X ^ 7 + (-X ^ 2 + 5 * X ^ 3 + 6 * X ^ 4 - 45 * X ^ 5 + 24 * X ^ 6) * S)
      * (2 - 16 * X + 32 * X ^ 2 : PowerSeries ℚ)⁻¹)

/-- The corrected recurrence for A174195. -/
theorem main : ∀ n : ℕ, 4 ≤ n →
    (4026 * (n : ℚ) ^ 3 - 12818 * (n : ℚ) ^ 2 + 41360 * (n : ℚ) + 166200) * a n
      + (4026 * (n : ℚ) ^ 3 - 128025 * (n : ℚ) ^ 2 + 34955 * (n : ℚ) + 59010) * a (n - 1)
      + (-80520 * (n : ℚ) ^ 3 + 644720 * (n : ℚ) ^ 2 - 1483826 * (n : ℚ) + 938190) * a (n - 2) = 0 := by
  sorry

end OMA.S_oeis_a174195

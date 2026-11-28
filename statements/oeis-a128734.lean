import Mathlib

/-!
# A128734: Number of LDs in all skew Dyck paths of semilength n.

Source: https://oeis.org/A128734
Credit: @ivillar

Status: open conjecture of the entry; it holds for the series as defined (a proof is filed with this statement).

The sequence (offset 0) begins 0, 0, 0, 1, 8, 48, 261, 1358, 6907, ...
The entry gives the generating function
  z^2*g^2*(g-1)/(1-3*z+2*z^2-3*z^2*g^2), where g = 1 + z*g^2 + z*(g-1) = (1 - z - sqrt(1 - 6*z + 5*z^2))/(2*z)
It is used here as the definition: a(n) is the coefficient of x^n of that series, where the square
root is the power series with constant term 1 (the binomial series (1 + X)^(1/2) evaluated at the
radicand minus 1), with R = 1-6*X+5*X^2 the radicand. Substituting g and rationalizing the denominator (multiplying by its conjugate under sqrt(R) -> -sqrt(R)) gives the form used below.
The series is written as (G) / (C * x^2) with C of nonzero constant term; the division by
x^2 is the shift of the index by 2. Expanding it reproduces the data of the entry.

The conjecture (R. J. Mathar, Jun 17 2016) reads
  Conjecture: +2*(3*n-20)*(n-3)*(n+1)*a(n) +(-39*n^3+362*n^2-739*n+300)*a(n-1) +8*(n-2) *(6*n^2-49*n+75) *a(n-2) -5*(n-2)*(n-3)*(3*n-17)*a(n-3)=0.
It involves a(n-3) and the offset is 0, so it is stated for n >= 3.
-/

namespace OMA.S_oeis_a128734

open PowerSeries

/-- The radicand of the generating function. -/
noncomputable def R : PowerSeries ℚ := 1 - 6 * X + 5 * X ^ 2

/-- The square root of the radicand with constant term 1: (1 + X)^(1/2) evaluated at R - 1. -/
noncomputable def S : PowerSeries ℚ := (PowerSeries.binomialSeries ℚ (1 / 2 : ℚ)).subst (R - 1)

/-- A128734: the coefficient of x^n in the generating function of the entry. -/
noncomputable def a (n : ℕ) : ℚ :=
  coeff (n + 2)
    ((-2 * X + 17 * X ^ 2 - 40 * X ^ 3 + 26 * X ^ 4 - 5 * X ^ 5 + (2 * X - 11 * X ^ 2 + 11 * X ^ 3 - 3 * X ^ 4) * S)
      * (8 - 48 * X + 42 * X ^ 2 - 10 * X ^ 3 : PowerSeries ℚ)⁻¹)

/-- The recurrence for A128734. -/
theorem main : ∀ n : ℕ, 3 ≤ n →
    (6 * (n : ℚ) ^ 3 - 52 * (n : ℚ) ^ 2 + 62 * (n : ℚ) + 120) * a n
      + (-39 * (n : ℚ) ^ 3 + 362 * (n : ℚ) ^ 2 - 739 * (n : ℚ) + 300) * a (n - 1)
      + (48 * (n : ℚ) ^ 3 - 488 * (n : ℚ) ^ 2 + 1384 * (n : ℚ) - 1200) * a (n - 2)
      + (-15 * (n : ℚ) ^ 3 + 160 * (n : ℚ) ^ 2 - 515 * (n : ℚ) + 510) * a (n - 3) = 0 := by
  sorry

end OMA.S_oeis_a128734

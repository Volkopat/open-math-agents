import Mathlib

/-!
# A119012: Number of valleys strictly above the x-axis in all hill-free Dyck paths of semilength n (a hill in a Dyck path is a peak at level 1).

Source: https://oeis.org/A119012
Credit: @vivanpoddar

The sequence (offset 1) begins 0, 0, 1, 5, 23, 98, 405, 1644, 6604, ...
The entry gives the generating function
  2*(1-3*z-(1-z)*sqrt(1-4*z))/((1+2*z+sqrt(1-4*z))^2*sqrt(1-4*z))
(see the entry). It is used here as the definition: a(n) is the coefficient of x^n of that series, where
the square root is the power series with constant term 1 (the binomial series (1 + X)^(1/2) evaluated
at the radicand minus 1). With R = 1 - 4*x the series is, in normalised form,
  (-4*x^4 - 7*x^3 - 2*x^2 + 5*x - 1 + (x^3 - 2*x^2 - 3*x + 1)*sqrt(R)) / (-8*x^5 - 30*x^4 - 24*x^3 + 8*x^2),
which is the expression used below (the division by x^2 is the shift of the index by 2).
Expanding it reproduces the data of the entry.

The conjecture (R. J. Mathar, Jun 22 2016) reads
  Conjecture: 2*(n-3)*(3*n-2)*(n+2)*a(n) +(-21*n^3+50*n^2-13*n-4)*a(n-1) -2*(n-1) *(2*n-1)*(3*n+1)*a(n-2)=0
It involves a(n-2) and the offset is 1, so it is stated for n >= 3.
-/

namespace OMA.S_oeis_a119012

open PowerSeries

/-- The radicand of the generating function. -/
noncomputable def R : PowerSeries ℚ := 1 - 4 * X

/-- The square root of the radicand with constant term 1: (1 + X)^(1/2) evaluated at R - 1. -/
noncomputable def S : PowerSeries ℚ := (PowerSeries.binomialSeries ℚ (1 / 2 : ℚ)).subst (R - 1)

/-- A119012: the coefficient of x^n in the generating function of the entry. -/
noncomputable def a (n : ℕ) : ℚ :=
  coeff (n + 2)
    ((-1 + 5 * X - 2 * X ^ 2 - 7 * X ^ 3 - 4 * X ^ 4 + (1 - 3 * X - 2 * X ^ 2 + X ^ 3) * S)
      * (8 - 24 * X - 30 * X ^ 2 - 8 * X ^ 3 : PowerSeries ℚ)⁻¹)

/-- The conjectured recurrence for A119012. -/
theorem main : ∀ n : ℕ, 3 ≤ n →
    (6 * (n : ℚ) ^ 3 - 10 * (n : ℚ) ^ 2 - 32 * (n : ℚ) + 24) * a n
      + (-21 * (n : ℚ) ^ 3 + 50 * (n : ℚ) ^ 2 - 13 * (n : ℚ) - 4) * a (n - 1)
      + (-12 * (n : ℚ) ^ 3 + 14 * (n : ℚ) ^ 2 - 2) * a (n - 2) = 0 := by
  sorry

end OMA.S_oeis_a119012

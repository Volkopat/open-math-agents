import Mathlib

/-!
# A191313: Sum of the abscissae of the first returns to the horizontal axis (assumed to be 0 if there are no such returns) in all dispersed Dyck paths of length n (i.e., Motzkin paths of length n with no (1,0) steps at positive heights).

Source: https://oeis.org/A191313
Credit: @ivillar

Status: open conjecture of the entry; it holds for the series as defined (a proof is filed with this statement).

The sequence (offset 0) begins 0, 0, 2, 5, 15, 30, 71, 134, 296, ...
The entry gives the generating function
  g = z*(4*z-1+q)/(q*(1-z)^2*(1-2*z+q)), where q=sqrt(1-4*z^2).
It is used here as the definition: a(n) is the coefficient of x^n of that series, where the square
root is the power series with constant term 1 (the binomial series (1 + X)^(1/2) evaluated at the
radicand minus 1), with R = 1-4*X^2 the radicand. Substituting and rationalizing
(multiplying by conjugates under sqrt(R) -> -sqrt(R)) and clearing denominators, the series is
(G) / (C * x^0) with polynomials G (linear in sqrt(R)) and C, C of nonzero constant term; the
division by x^0 is the shift of the index by 0. Expanding it reproduces the data of the entry.

The conjecture (R. J. Mathar, Jun 14 2016) reads
  Conjecture: n*(3*n-13)*a(n) +2*(-6*n^2+29*n-18)*a(n-1) +(3*n^2-13*n+24)*a(n-2) +2*(21*n^2-124*n+150)*a(n-3) +4*(-15*n^2+92*n-132) *a(n-4) +8*(n-3)*(3*n-10) *a(n-5)=0.
It involves a(n-5) and the offset is 0, so it is stated for n >= 5.
-/

namespace OMA.S_oeis_a191313

open PowerSeries

/-- The radicand of the generating function. -/
noncomputable def R : PowerSeries ℚ := 1 - 4 * X ^ 2

/-- The square root of the radicand with constant term 1: (1 + X)^(1/2) evaluated at R - 1. -/
noncomputable def S : PowerSeries ℚ := (PowerSeries.binomialSeries ℚ (1 / 2 : ℚ)).subst (R - 1)

/-- A191313: the coefficient of x^n in the generating function of the entry. -/
noncomputable def a (n : ℕ) : ℚ :=
  coeff n
    ((-1 + 4 * X + X ^ 2 - 16 * X ^ 3 + 12 * X ^ 4 + (1 - 4 * X + 5 * X ^ 2 - 2 * X ^ 3) * S)
      * (2 - 10 * X + 10 * X ^ 2 + 26 * X ^ 3 - 68 * X ^ 4 + 56 * X ^ 5 - 16 * X ^ 6 : PowerSeries ℚ)⁻¹)

/-- The recurrence for A191313. -/
theorem main : ∀ n : ℕ, 5 ≤ n →
    (3 * (n : ℚ) ^ 2 - 13 * (n : ℚ)) * a n + (-12 * (n : ℚ) ^ 2 + 58 * (n : ℚ) - 36) * a (n - 1)
      + (3 * (n : ℚ) ^ 2 - 13 * (n : ℚ) + 24) * a (n - 2)
      + (42 * (n : ℚ) ^ 2 - 248 * (n : ℚ) + 300) * a (n - 3)
      + (-60 * (n : ℚ) ^ 2 + 368 * (n : ℚ) - 528) * a (n - 4)
      + (24 * (n : ℚ) ^ 2 - 152 * (n : ℚ) + 240) * a (n - 5) = 0 := by
  sorry

end OMA.S_oeis_a191313

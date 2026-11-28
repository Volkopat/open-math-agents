import Mathlib

/-!
# A191309: Number of peaks at height >= 2 in all dispersed Dyck paths of length n (i.e., Motzkin paths of length n with no (1,0) steps at positive heights).

Source: https://oeis.org/A191309
Credit: @ivillar

Status: open conjecture of the entry; it holds for the series as defined (a proof is filed with this statement).

The sequence (offset 0) begins 0, 0, 0, 0, 1, 2, 8, 16, 47, ...
The entry gives the generating function
  g = 2*z^2*(1-q)/(q*(1-2*z+q)^2), where q=sqrt(1-4*z^2).
It is used here as the definition: a(n) is the coefficient of x^n of that series, where the square
root is the power series with constant term 1 (the binomial series (1 + X)^(1/2) evaluated at the
radicand minus 1), with R = 1-4*X^2 the radicand. Substituting and rationalizing
(multiplying by conjugates under sqrt(R) -> -sqrt(R)) and clearing denominators, the series is
(G) / (C * x^0) with polynomials G (linear in sqrt(R)) and C, C of nonzero constant term; the
division by x^0 is the shift of the index by 0. Expanding it reproduces the data of the entry.

The conjecture (R. J. Mathar, Jun 14 2016) reads
  Conjecture: n*(n-4)*a(n) +(n^2-10*n+15)*a(n-1) +2*(-5*n^2+28*n-27)*a(n-2) -4*(n-3)*(n-8) *a(n-3) +24*(n-3)*(n-4)*a(n-4)=0.
It involves a(n-4) and the offset is 0, so it is stated for n >= 4.
-/

namespace OMA.S_oeis_a191309

open PowerSeries

/-- The radicand of the generating function. -/
noncomputable def R : PowerSeries ℚ := 1 - 4 * X ^ 2

/-- The square root of the radicand with constant term 1: (1 + X)^(1/2) evaluated at R - 1. -/
noncomputable def S : PowerSeries ℚ := (PowerSeries.binomialSeries ℚ (1 / 2 : ℚ)).subst (R - 1)

/-- A191309: the coefficient of x^n in the generating function of the entry. -/
noncomputable def a (n : ℕ) : ℚ :=
  coeff n
    ((-1 + 2 * X + 4 * X ^ 2 - 8 * X ^ 3 + (1 - 2 * X - 2 * X ^ 2 + 4 * X ^ 3) * S)
      * (2 - 8 * X + 32 * X ^ 3 - 32 * X ^ 4 : PowerSeries ℚ)⁻¹)

/-- The recurrence for A191309. -/
theorem main : ∀ n : ℕ, 4 ≤ n →
    ((n : ℚ) ^ 2 - 4 * (n : ℚ)) * a n + ((n : ℚ) ^ 2 - 10 * (n : ℚ) + 15) * a (n - 1)
      + (-10 * (n : ℚ) ^ 2 + 56 * (n : ℚ) - 54) * a (n - 2)
      + (-4 * (n : ℚ) ^ 2 + 44 * (n : ℚ) - 96) * a (n - 3)
      + (24 * (n : ℚ) ^ 2 - 168 * (n : ℚ) + 288) * a (n - 4) = 0 := by
  sorry

end OMA.S_oeis_a191309

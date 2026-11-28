import Mathlib

/-!
# A268399: Number of North-East lattice paths from (0,0) to (n,n) that have exactly four east steps below the subdiagonal y = x-1.

Source: https://oeis.org/A268399
Credit: @vivanpoddar

The sequence (offset 5) begins 14, 70, 286, 1099, 4124, 15327, 56770, 210188, 779076, ...
The entry gives the generating function
  -((-1 + f + 2*x)^2*(-1 + f + x*(2*f + x + 5*f*x - 10*x^2)))/(8*x^2), where f = sqrt(1 - 4*x)
(see the entry). It is used here as the definition: a(n) is the coefficient of x^n of that series, where
the square root is the power series with constant term 1 (the binomial series (1 + X)^(1/2) evaluated
at the radicand minus 1). With R = 1 - 4*x the series is, in normalised form,
  (10*x^5 - x^4 + x^2 - 4*x + 1 + (5*x^4 + 2*x^3 + x^2 + 2*x - 1)*sqrt(R)) / (2*x^2),
which is the expression used below (the division by x^2 is the shift of the index by 2).
Expanding it reproduces the data of the entry.

The conjecture (R. J. Mathar, Jun 07 2016) reads
  Conjecture: -(n+2)*(641*n-5292)*a(n) +(-641*n^2-1681*n+22692)*a(n-1) +(-4067*n^2+10502*n+80184) *a(n-2) +6*(5629*n-11668)*(2*n-11) *a(n-3)=0
It involves a(n-3) and the offset is 5, so it is stated for n >= 8.
-/

namespace OMA.S_oeis_a268399

open PowerSeries

/-- The radicand of the generating function. -/
noncomputable def R : PowerSeries ℚ := 1 - 4 * X

/-- The square root of the radicand with constant term 1: (1 + X)^(1/2) evaluated at R - 1. -/
noncomputable def S : PowerSeries ℚ := (PowerSeries.binomialSeries ℚ (1 / 2 : ℚ)).subst (R - 1)

/-- A268399: the coefficient of x^n in the generating function of the entry. -/
noncomputable def a (n : ℕ) : ℚ :=
  coeff (n + 2)
    ((1 - 4 * X + X ^ 2 - X ^ 4 + 10 * X ^ 5 + (-1 + 2 * X + X ^ 2 + 2 * X ^ 3 + 5 * X ^ 4) * S)
      * (2 : PowerSeries ℚ)⁻¹)

/-- The conjectured recurrence for A268399. -/
theorem main : ∀ n : ℕ, 8 ≤ n →
    (-641 * (n : ℚ) ^ 2 + 4010 * (n : ℚ) + 10584) * a n
      + (-641 * (n : ℚ) ^ 2 - 1681 * (n : ℚ) + 22692) * a (n - 1)
      + (-4067 * (n : ℚ) ^ 2 + 10502 * (n : ℚ) + 80184) * a (n - 2)
      + (67548 * (n : ℚ) ^ 2 - 511530 * (n : ℚ) + 770088) * a (n - 3) = 0 := by
  sorry

end OMA.S_oeis_a268399

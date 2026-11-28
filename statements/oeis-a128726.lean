import Mathlib

/-!
# A128726: Number of LL's in all skew Dyck paths of semilength n.

Source: https://oeis.org/A128726
Credit: @ivillar

Status: open conjecture of the entry; it holds for the series as defined (a proof is filed with this statement).

The sequence (offset 0) begins 0, 0, 0, 1, 7, 38, 192, 946, 4616, ...
The entry gives the generating function
  z(1-g+zg^2)/[(1-z-zg)(1+z-3zg)], where g=1+zg^2+z(g-1)=[1-z-sqrt(1-6z+5z^2)]/(2z)
It is used here as the definition: a(n) is the coefficient of x^n of that series, where the square
root is the power series with constant term 1 (the binomial series (1 + X)^(1/2) evaluated at the
radicand minus 1), with R = 1-6*X+5*X^2 the radicand. As printed, this expression expands to the negatives of the terms (its x^3 coefficient is -1 while a(3) = 1), so its negative is used. Substituting g and rationalizing (multiplying by conjugates under sqrt(R) -> -sqrt(R)) gives the form used below. The recurrence is linear and homogeneous, so the sign does not affect it.
The series is written as (G) / (C * x^0) with C of nonzero constant term; the division by
x^0 is the shift of the index by 0. Expanding it reproduces the data of the entry.

The conjecture (R. J. Mathar, Jun 17 2016) reads
  Conjecture: +2*n*(n-3)^2*a(n) +(-13*n^3+84*n^2-167*n+100)*a(n-1) +(n-2)*(16*n^2-77*n+85)*a(n-2) -5*(n-3)*(n-2)^2*a(n-3)=0.
It involves a(n-3) and the offset is 0, so it is stated for n >= 3.
-/

namespace OMA.S_oeis_a128726

open PowerSeries

/-- The radicand of the generating function. -/
noncomputable def R : PowerSeries ℚ := 1 - 6 * X + 5 * X ^ 2

/-- The square root of the radicand with constant term 1: (1 + X)^(1/2) evaluated at R - 1. -/
noncomputable def S : PowerSeries ℚ := (PowerSeries.binomialSeries ℚ (1 / 2 : ℚ)).subst (R - 1)

/-- A128726: the coefficient of x^n in the generating function of the entry. -/
noncomputable def a (n : ℕ) : ℚ :=
  coeff n
    ((-2 + 15 * X - 29 * X ^ 2 + 21 * X ^ 3 - 5 * X ^ 4 + (2 - 9 * X + 6 * X ^ 2 - X ^ 3) * S)
      * (8 - 56 * X + 90 * X ^ 2 - 52 * X ^ 3 + 10 * X ^ 4 : PowerSeries ℚ)⁻¹)

/-- The recurrence for A128726. -/
theorem main : ∀ n : ℕ, 3 ≤ n →
    (2 * (n : ℚ) ^ 3 - 12 * (n : ℚ) ^ 2 + 18 * (n : ℚ)) * a n
      + (-13 * (n : ℚ) ^ 3 + 84 * (n : ℚ) ^ 2 - 167 * (n : ℚ) + 100) * a (n - 1)
      + (16 * (n : ℚ) ^ 3 - 109 * (n : ℚ) ^ 2 + 239 * (n : ℚ) - 170) * a (n - 2)
      + (-5 * (n : ℚ) ^ 3 + 35 * (n : ℚ) ^ 2 - 80 * (n : ℚ) + 60) * a (n - 3) = 0 := by
  sorry

end OMA.S_oeis_a128726

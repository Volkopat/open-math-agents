import Mathlib

/-!
# A127154: Number of Dyck paths of semilength n and having no UDUD's starting at level 0; here U=(1,1), D=(1,-1).

Source: https://oeis.org/A127154
Credit: @vivanpoddar

The sequence (offset 0) begins 1, 1, 1, 4, 11, 33, 105, 343, 1148, ...
The entry gives the generating function
  2*(1+x)/(1+x+2*x^2+(1+x)*sqrt(1-4*x))
(see the entry). It is used here as the definition: a(n) is the coefficient of x^n of that series, where
the square root is the power series with constant term 1 (the binomial series (1 + X)^(1/2) evaluated
at the radicand minus 1). With R = 1 - 4*x the series is, in normalised form,
  (2*x^3 + 3*x^2 + 2*x + 1 + (-x^2 - 2*x - 1)*sqrt(R)) / (2*x^4 + 4*x^3 + 6*x^2 + 2*x),
which is the expression used below (the division by x^1 is the shift of the index by 1).
Expanding it reproduces the data of the entry.

The conjecture (R. J. Mathar, Jun 17 2016) reads
  Conjecture: (n+1)*a(n) +3*a(n-1) +(-11*n+16)*a(n-2) +(-17*n+43)*a(n-3) +(-11*n+28)*a(n-4) +2*(-2*n+7)*a(n-5)=0
It involves a(n-5) and the offset is 0, so it is stated for n >= 5.
-/

namespace OMA.S_oeis_a127154

open PowerSeries

/-- The radicand of the generating function. -/
noncomputable def R : PowerSeries ℚ := 1 - 4 * X

/-- The square root of the radicand with constant term 1: (1 + X)^(1/2) evaluated at R - 1. -/
noncomputable def S : PowerSeries ℚ := (PowerSeries.binomialSeries ℚ (1 / 2 : ℚ)).subst (R - 1)

/-- A127154: the coefficient of x^n in the generating function of the entry. -/
noncomputable def a (n : ℕ) : ℚ :=
  coeff (n + 1)
    ((1 + 2 * X + 3 * X ^ 2 + 2 * X ^ 3 + (-1 - 2 * X - X ^ 2) * S)
      * (2 + 6 * X + 4 * X ^ 2 + 2 * X ^ 3 : PowerSeries ℚ)⁻¹)

/-- The conjectured recurrence for A127154. -/
theorem main : ∀ n : ℕ, 5 ≤ n →
    ((n : ℚ) + 1) * a n + (3) * a (n - 1) + (-11 * (n : ℚ) + 16) * a (n - 2)
      + (-17 * (n : ℚ) + 43) * a (n - 3) + (-11 * (n : ℚ) + 28) * a (n - 4)
      + (-4 * (n : ℚ) + 14) * a (n - 5) = 0 := by
  sorry

end OMA.S_oeis_a127154

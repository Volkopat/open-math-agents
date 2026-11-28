import Mathlib

/-!
# A128723: Number of skew Dyck paths of semilength n having no peaks at level 1.

Source: https://oeis.org/A128723
Credit: @vivanpoddar

The sequence (offset 0) begins 1, 0, 2, 6, 22, 84, 334, 1368, 5734, ...
The entry gives the generating function
  (3-3*z-sqrt(1-6*z+5*z^2))/(1+3*z+sqrt(1-6*z+5*z^2))
(see the entry). It is used here as the definition: a(n) is the coefficient of x^n of that series, where
the square root is the power series with constant term 1 (the binomial series (1 + X)^(1/2) evaluated
at the radicand minus 1). With R = 5*x^2 - 6*x + 1 the series is, in normalised form,
  (1 - x^2 + (-1)*sqrt(R)) / (x^2 + 3*x),
which is the expression used below (the division by x^1 is the shift of the index by 1).
Expanding it reproduces the data of the entry.

The conjecture (R. J. Mathar, Jun 17 2016) reads
  Conjecture: +3*(n+1)*a(n) +(-17*n+10)*a(n-1) +9*(n-3)*a(n-2) +5*(n-2)*a(n-3)=0
The recurrence fails for n in [3] (small n, where the inhomogeneous part of the differential
equation is felt), so it is stated for n >= 4.
-/

namespace OMA.S_oeis_a128723

open PowerSeries

/-- The radicand of the generating function. -/
noncomputable def R : PowerSeries ℚ := 1 - 6 * X + 5 * X ^ 2

/-- The square root of the radicand with constant term 1: (1 + X)^(1/2) evaluated at R - 1. -/
noncomputable def S : PowerSeries ℚ := (PowerSeries.binomialSeries ℚ (1 / 2 : ℚ)).subst (R - 1)

/-- A128723: the coefficient of x^n in the generating function of the entry. -/
noncomputable def a (n : ℕ) : ℚ :=
  coeff (n + 1)
    ((1 - X ^ 2 - S)
      * (3 + X : PowerSeries ℚ)⁻¹)

/-- The conjectured recurrence for A128723. -/
theorem main : ∀ n : ℕ, 4 ≤ n →
    (3 * (n : ℚ) + 3) * a n + (-17 * (n : ℚ) + 10) * a (n - 1) + (9 * (n : ℚ) - 27) * a (n - 2)
      + (5 * (n : ℚ) - 10) * a (n - 3) = 0 := by
  sorry

end OMA.S_oeis_a128723

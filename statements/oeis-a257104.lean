import Mathlib

/-!
# A257104: Number of Motzkin paths of length n with no peaks at level 3.

Source: https://oeis.org/A257104
Credit: @vivanpoddar

The sequence (offset 0) begins 1, 1, 2, 4, 9, 21, 50, 121, 297, ...
The entry gives the generating function
  1/(1 - x - x^2/(1 - x - x^2/(1 - x + x^2*(1 - M(x))))), where M(x) = (1 - x - sqrt(1 - 2*x - 3*x^2))/(2*x^2) is the g.f. of the Motzkin numbers A001006
(see the entry). It is used here as the definition: a(n) is the coefficient of x^n of that series, where
the square root is the power series with constant term 1 (the binomial series (1 + X)^(1/2) evaluated
at the radicand minus 1). With R = -3*x^2 - 2*x + 1 the series is, in normalised form,
  (2*x^4 - 3*x^3 + 9*x^2 - 8*x + 2 + (-x^2)*sqrt(R)) / (2*x^4 - 4*x^3 + 14*x^2 - 10*x + 2),
which is the expression used below (the division by x^0 is the shift of the index by 0).
Expanding it reproduces the data of the entry.

The conjecture (R. J. Mathar, Sep 24 2016) reads
  Conjecture: D-finite with recurrence (-n+2)*a(n) +(7*n-17)*a(n-1) +2*(-7*n+17)*a(n-2) +(n+22)*a(n-3) +(16*n-89)*a(n-4) +(-4*n+23)*a(n-5) +3*(n-5)*a(n-6)=0
The recurrence fails for n in [6] (small n, where the inhomogeneous part of the differential
equation is felt), so it is stated for n >= 7.
-/

namespace OMA.S_oeis_a257104

open PowerSeries

/-- The radicand of the generating function. -/
noncomputable def R : PowerSeries ℚ := 1 - 2 * X - 3 * X ^ 2

/-- The square root of the radicand with constant term 1: (1 + X)^(1/2) evaluated at R - 1. -/
noncomputable def S : PowerSeries ℚ := (PowerSeries.binomialSeries ℚ (1 / 2 : ℚ)).subst (R - 1)

/-- A257104: the coefficient of x^n in the generating function of the entry. -/
noncomputable def a (n : ℕ) : ℚ :=
  coeff n
    ((2 - 8 * X + 9 * X ^ 2 - 3 * X ^ 3 + 2 * X ^ 4 + (-X ^ 2) * S)
      * (2 - 10 * X + 14 * X ^ 2 - 4 * X ^ 3 + 2 * X ^ 4 : PowerSeries ℚ)⁻¹)

/-- The conjectured recurrence for A257104. -/
theorem main : ∀ n : ℕ, 7 ≤ n →
    (-(n : ℚ) + 2) * a n + (7 * (n : ℚ) - 17) * a (n - 1) + (-14 * (n : ℚ) + 34) * a (n - 2)
      + ((n : ℚ) + 22) * a (n - 3) + (16 * (n : ℚ) - 89) * a (n - 4)
      + (-4 * (n : ℚ) + 23) * a (n - 5) + (3 * (n : ℚ) - 15) * a (n - 6) = 0 := by
  sorry

end OMA.S_oeis_a257104

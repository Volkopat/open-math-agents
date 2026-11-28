import Mathlib

/-!
# A103137: First column of inverse of Delannoy triangle.

Source: https://oeis.org/A103137
Credit: @vivanpoddar

The sequence (offset 0) begins 1, -1, 2, -6, 22, -90, 394, -1806, 8558, ...
The entry gives the generating function
  1 - x*S(-x), where S(x) = (1 - x - sqrt(1 - 6*x + x^2))/(2*x) is the g.f. of the large Schroeder numbers A006318
(see the entry). It is used here as the definition: a(n) is the coefficient of x^n of that series, where
the square root is the power series with constant term 1 (the binomial series (1 + X)^(1/2) evaluated
at the radicand minus 1). With R = x^2 + 6*x + 1 the series is, in normalised form,
  (x + 3 + (-1)*sqrt(R)) / (2),
which is the expression used below (the division by x^0 is the shift of the index by 0).
Expanding it reproduces the data of the entry.

The conjecture (R. J. Mathar, Nov 26 2012) reads
  Conjecture: n*a(n) +3*(2*n-3)*a(n-1) +(n-3)*a(n-2)=0
It involves a(n-2) and the offset is 0, so it is stated for n >= 2.
-/

namespace OMA.S_oeis_a103137

open PowerSeries

/-- The radicand of the generating function. -/
noncomputable def R : PowerSeries ℚ := 1 + 6 * X + X ^ 2

/-- The square root of the radicand with constant term 1: (1 + X)^(1/2) evaluated at R - 1. -/
noncomputable def S : PowerSeries ℚ := (PowerSeries.binomialSeries ℚ (1 / 2 : ℚ)).subst (R - 1)

/-- A103137: the coefficient of x^n in the generating function of the entry. -/
noncomputable def a (n : ℕ) : ℚ :=
  coeff n
    ((3 + X - S)
      * (2 : PowerSeries ℚ)⁻¹)

/-- The conjectured recurrence for A103137. -/
theorem main : ∀ n : ℕ, 2 ≤ n →
    (n : ℚ) * a n + (6 * (n : ℚ) - 9) * a (n - 1) + ((n : ℚ) - 3) * a (n - 2) = 0 := by
  sorry

end OMA.S_oeis_a103137

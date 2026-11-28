import Mathlib

/-!
# A108600: Number of freely braided permutations of length n; the freely braided permutations are those that avoid 3421, 4231, 4312 and 4321.

Source: https://oeis.org/A108600
Credit: @vivanpoddar

The sequence (offset 0) begins 1, 1, 2, 6, 20, 71, 260, 971, 3674, ...
The entry gives the generating function
  (1-3*x-2*x^2+(1+x)*sqrt(1-4*x)) / (1-4*x-x^2+(1-x^2)*sqrt(1-4*x))
(see the entry). It is used here as the definition: a(n) is the coefficient of x^n of that series, where
the square root is the power series with constant term 1 (the binomial series (1 + X)^(1/2) evaluated
at the radicand minus 1). With R = 1 - 4*x the series is, in normalised form,
  (x^3 - 4*x^2 - 7*x + 2 + (x^3 + 2*x^2 + x)*sqrt(R)) / (-2*x^4 - 8*x + 2),
which is the expression used below (the division by x^0 is the shift of the index by 0).
Expanding it reproduces the data of the entry.

The conjecture (R. J. Mathar, Aug 24 2013) reads
  Conjecture: (1-n)*a(n) +(7*n-10)*a(n-1) +2*(1-4*n)*a(n-2) +8*(11-2*n)*a(n-3) +(n-1)*a(n-4) +3*(2-n)*a(n-5) +2*(11-2*n)*a(n-6)=0
It involves a(n-6) and the offset is 0, so it is stated for n >= 6.
-/

namespace OMA.S_oeis_a108600

open PowerSeries

/-- The radicand of the generating function. -/
noncomputable def R : PowerSeries ℚ := 1 - 4 * X

/-- The square root of the radicand with constant term 1: (1 + X)^(1/2) evaluated at R - 1. -/
noncomputable def S : PowerSeries ℚ := (PowerSeries.binomialSeries ℚ (1 / 2 : ℚ)).subst (R - 1)

/-- A108600: the coefficient of x^n in the generating function of the entry. -/
noncomputable def a (n : ℕ) : ℚ :=
  coeff n
    ((2 - 7 * X - 4 * X ^ 2 + X ^ 3 + (X + 2 * X ^ 2 + X ^ 3) * S)
      * (2 - 8 * X - 2 * X ^ 4 : PowerSeries ℚ)⁻¹)

/-- The conjectured recurrence for A108600. -/
theorem main : ∀ n : ℕ, 6 ≤ n →
    (-(n : ℚ) + 1) * a n + (7 * (n : ℚ) - 10) * a (n - 1) + (-8 * (n : ℚ) + 2) * a (n - 2)
      + (-16 * (n : ℚ) + 88) * a (n - 3) + ((n : ℚ) - 1) * a (n - 4)
      + (-3 * (n : ℚ) + 6) * a (n - 5) + (-4 * (n : ℚ) + 22) * a (n - 6) = 0 := by
  sorry

end OMA.S_oeis_a108600

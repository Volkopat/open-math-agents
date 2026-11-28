import Mathlib

/-!
# A116383: Row sums of number triangle A116382.

Source: https://oeis.org/A116383
Credit: @vivanpoddar

The sequence (offset 0) begins 1, 1, 4, 6, 19, 33, 93, 175, 460, ...
The entry gives the generating function
  (1+x-4*x^2)/(2*(1-5*x^2)*sqrt(1-4*x^2)) + (1+x)/(2*(1-5*x^2))
(see the entry). It is used here as the definition: a(n) is the coefficient of x^n of that series, where
the square root is the power series with constant term 1 (the binomial series (1 + X)^(1/2) evaluated
at the radicand minus 1). With R = 1 - 4*x^2 the series is, in normalised form,
  (-4*x^3 - 4*x^2 + x + 1 + (-4*x^2 + x + 1)*sqrt(R)) / (40*x^4 - 18*x^2 + 2),
which is the expression used below (the division by x^0 is the shift of the index by 0).
Expanding it reproduces the data of the entry.

The conjecture (R. J. Mathar, Nov 24 2012) reads
  Conjecture: n*a(n) + (n-2)*a(n-1) + (-13*n+20)*a(n-2) + (-9*n+22)*a(n-3) + 4*(14*n-45)*a(n-4) + 20*(n-3)*a(n-5) + 80*(-n+5)*a(n-6) = 0
It involves a(n-6) and the offset is 0, so it is stated for n >= 6.
-/

namespace OMA.S_oeis_a116383

open PowerSeries

/-- The radicand of the generating function. -/
noncomputable def R : PowerSeries ℚ := 1 - 4 * X ^ 2

/-- The square root of the radicand with constant term 1: (1 + X)^(1/2) evaluated at R - 1. -/
noncomputable def S : PowerSeries ℚ := (PowerSeries.binomialSeries ℚ (1 / 2 : ℚ)).subst (R - 1)

/-- A116383: the coefficient of x^n in the generating function of the entry. -/
noncomputable def a (n : ℕ) : ℚ :=
  coeff n
    ((1 + X - 4 * X ^ 2 - 4 * X ^ 3 + (1 + X - 4 * X ^ 2) * S)
      * (2 - 18 * X ^ 2 + 40 * X ^ 4 : PowerSeries ℚ)⁻¹)

/-- The conjectured recurrence for A116383. -/
theorem main : ∀ n : ℕ, 6 ≤ n →
    (n : ℚ) * a n + ((n : ℚ) - 2) * a (n - 1) + (-13 * (n : ℚ) + 20) * a (n - 2)
      + (-9 * (n : ℚ) + 22) * a (n - 3) + (56 * (n : ℚ) - 180) * a (n - 4)
      + (20 * (n : ℚ) - 60) * a (n - 5) + (-80 * (n : ℚ) + 400) * a (n - 6) = 0 := by
  sorry

end OMA.S_oeis_a116383

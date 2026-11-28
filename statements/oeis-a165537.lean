import Mathlib

/-!
# A165537: Number of permutations of length n which avoid the patterns 4213 and 2143.

Source: https://oeis.org/A165537
Credit: @vivanpoddar

The sequence (offset 0) begins 1, 1, 2, 6, 22, 88, 366, 1556, 6720, ...
The entry gives the generating function
  1 + ((1-2*z) * (-1 + 5*z - 7*z^2 + 2*z^3 + (1-z)*sqrt(1 - 6*z + 5*z^2))) / (1 - 10*z + 24*z^2 - 20*z^3 + 4*z^4)
(David Bevan, Sep 25 2015). It is used here as the definition: a(n) is the coefficient of x^n of that series, where
the square root is the power series with constant term 1 (the binomial series (1 + X)^(1/2) evaluated
at the radicand minus 1). With R = 5*x^2 - 6*x + 1 the series is, in normalised form,
  (-4*x^3 + 7*x^2 - 3*x + (2*x^2 - 3*x + 1)*sqrt(R)) / (4*x^4 - 20*x^3 + 24*x^2 - 10*x + 1),
which is the expression used below (the division by x^0 is the shift of the index by 0).
Expanding it reproduces the data of the entry.

The conjecture (R. J. Mathar, Jun 14 2016) reads
  Conjecture: n*a(n) + 2*(-9*n+7)*a(n-1) + (121*n-204)*a(n-2) + 28*(-14*n+37)*a(n-3) + 16*(42*n-151)*a(n-4) + 4*(-153*n+694)*a(n-5) + 4*(67*n-364)*a(n-6) + 40*(-n+6)*a(n-7) = 0
It involves a(n-7) and the offset is 0, so it is stated for n >= 7.
-/

namespace OMA.S_oeis_a165537

open PowerSeries

/-- The radicand of the generating function. -/
noncomputable def R : PowerSeries ℚ := 1 - 6 * X + 5 * X ^ 2

/-- The square root of the radicand with constant term 1: (1 + X)^(1/2) evaluated at R - 1. -/
noncomputable def S : PowerSeries ℚ := (PowerSeries.binomialSeries ℚ (1 / 2 : ℚ)).subst (R - 1)

/-- A165537: the coefficient of x^n in the generating function of the entry. -/
noncomputable def a (n : ℕ) : ℚ :=
  coeff n
    ((-3 * X + 7 * X ^ 2 - 4 * X ^ 3 + (1 - 3 * X + 2 * X ^ 2) * S)
      * (1 - 10 * X + 24 * X ^ 2 - 20 * X ^ 3 + 4 * X ^ 4 : PowerSeries ℚ)⁻¹)

/-- The conjectured recurrence for A165537. -/
theorem main : ∀ n : ℕ, 7 ≤ n →
    (n : ℚ) * a n + (-18 * (n : ℚ) + 14) * a (n - 1) + (121 * (n : ℚ) - 204) * a (n - 2)
      + (-392 * (n : ℚ) + 1036) * a (n - 3) + (672 * (n : ℚ) - 2416) * a (n - 4)
      + (-612 * (n : ℚ) + 2776) * a (n - 5) + (268 * (n : ℚ) - 1456) * a (n - 6)
      + (-40 * (n : ℚ) + 240) * a (n - 7) = 0 := by
  sorry

end OMA.S_oeis_a165537

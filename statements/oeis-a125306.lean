import Mathlib

/-!
# A125306: Number of 123-segmented permutations of length n.

Source: https://oeis.org/A125306
Credit: @vivanpoddar

The sequence (offset 0) begins 1, 1, 2, 6, 18, 56, 182, 607, 2064, ...
The entry gives the generating function
  1 + (C(x) - 1)/(1 - x/(1 + x^2) * (C(x) - 1))
(see the entry). It is used here as the definition: a(n) is the coefficient of x^n of that series, where
the square root is the power series with constant term 1 (the binomial series (1 + X)^(1/2) evaluated
at the radicand minus 1). With R = 1 - 4*x the series is, in normalised form,
  (3*x^4 + 4*x^2 - 2*x + 1 + (-x^4 - 2*x^2 - 1)*sqrt(R)) / (2*x^5 + 4*x^4 + 4*x^3 + 4*x^2),
which is the expression used below (the division by x^2 is the shift of the index by 2).
Expanding it reproduces the data of the entry.

The conjecture (R. J. Mathar, May 30 2014) reads
  Conjecture: 2*(n+2)*a(n) - 6*n*a(n-1) + 4*(-n-2)*a(n-2) + (-13*n+34)*a(n-3) + 2*(-5*n+17)*a(n-4) + (-7*n+40)*a(n-5) + 2*(-2*n+11)*a(n-6) = 0
It involves a(n-6) and the offset is 0, so it is stated for n >= 6.
-/

namespace OMA.S_oeis_a125306

open PowerSeries

/-- The radicand of the generating function. -/
noncomputable def R : PowerSeries ℚ := 1 - 4 * X

/-- The square root of the radicand with constant term 1: (1 + X)^(1/2) evaluated at R - 1. -/
noncomputable def S : PowerSeries ℚ := (PowerSeries.binomialSeries ℚ (1 / 2 : ℚ)).subst (R - 1)

/-- A125306: the coefficient of x^n in the generating function of the entry. -/
noncomputable def a (n : ℕ) : ℚ :=
  coeff (n + 2)
    ((1 - 2 * X + 4 * X ^ 2 + 3 * X ^ 4 + (-1 - 2 * X ^ 2 - X ^ 4) * S)
      * (4 + 4 * X + 4 * X ^ 2 + 2 * X ^ 3 : PowerSeries ℚ)⁻¹)

/-- The conjectured recurrence for A125306. -/
theorem main : ∀ n : ℕ, 6 ≤ n →
    (2 * (n : ℚ) + 4) * a n + (-6 * (n : ℚ)) * a (n - 1) + (-4 * (n : ℚ) - 8) * a (n - 2)
      + (-13 * (n : ℚ) + 34) * a (n - 3) + (-10 * (n : ℚ) + 34) * a (n - 4)
      + (-7 * (n : ℚ) + 40) * a (n - 5) + (-4 * (n : ℚ) + 22) * a (n - 6) = 0 := by
  sorry

end OMA.S_oeis_a125306

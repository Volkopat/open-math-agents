import Mathlib

/-!
# A171416: A sequence with Somos-4 Hankel transform.

Source: https://oeis.org/A171416
Credit: @vivanpoddar

The sequence (offset 0) begins 1, 1, 2, 3, 7, 13, 31, 65, 156, ...
The entry gives the generating function
  (1 - x^2 - sqrt(1-6*x^2-4*x^3+x^4))/(2*x^2)
(see the entry). It is used here as the definition: a(n) is the coefficient of x^n of that series, where
the square root is the power series with constant term 1 (the binomial series (1 + X)^(1/2) evaluated
at the radicand minus 1). With R = x^4 - 4*x^3 - 6*x^2 + 1 the series is, in normalised form,
  (1 - x^2 + (-1)*sqrt(R)) / (2*x^2),
which is the expression used below (the division by x^2 is the shift of the index by 2).
Expanding it reproduces the data of the entry.

The conjecture (R. J. Mathar, Jul 24 2012) reads
  Conjecture: (n+2)*a(n) +(n+1)*a(n-1) +6*(1-n)*a(n-2) +2*(11-5*n)*a(n-3) +(10-3*n)*a(n-4) +(n-5)*a(n-5)=0
It involves a(n-5) and the offset is 0, so it is stated for n >= 5.
-/

namespace OMA.S_oeis_a171416

open PowerSeries

/-- The radicand of the generating function. -/
noncomputable def R : PowerSeries ℚ := 1 - 6 * X ^ 2 - 4 * X ^ 3 + X ^ 4

/-- The square root of the radicand with constant term 1: (1 + X)^(1/2) evaluated at R - 1. -/
noncomputable def S : PowerSeries ℚ := (PowerSeries.binomialSeries ℚ (1 / 2 : ℚ)).subst (R - 1)

/-- A171416: the coefficient of x^n in the generating function of the entry. -/
noncomputable def a (n : ℕ) : ℚ :=
  coeff (n + 2)
    ((1 - X ^ 2 - S)
      * (2 : PowerSeries ℚ)⁻¹)

/-- The conjectured recurrence for A171416. -/
theorem main : ∀ n : ℕ, 5 ≤ n →
    ((n : ℚ) + 2) * a n + ((n : ℚ) + 1) * a (n - 1) + (-6 * (n : ℚ) + 6) * a (n - 2)
      + (-10 * (n : ℚ) + 22) * a (n - 3) + (-3 * (n : ℚ) + 10) * a (n - 4)
      + ((n : ℚ) - 5) * a (n - 5) = 0 := by
  sorry

end OMA.S_oeis_a171416

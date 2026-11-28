import Mathlib

/-!
# A174016: Row sums of number triangle A174014.

Source: https://oeis.org/A174016
Credit: @vivanpoddar

The sequence (offset 0) begins 1, 2, 6, 16, 40, 92, 192, 352, 528, ...
The entry gives the generating function
  (sqrt(1-4x+4x^2+8x^3)+4x-1)/(2x(1-2x))
(see the entry). It is used here as the definition: a(n) is the coefficient of x^n of that series, where
the square root is the power series with constant term 1 (the binomial series (1 + X)^(1/2) evaluated
at the radicand minus 1). With R = 8*x^3 + 4*x^2 - 4*x + 1 the series is, in normalised form,
  (4*x - 1 + (1)*sqrt(R)) / (-4*x^2 + 2*x),
which is the expression used below (the division by x^1 is the shift of the index by 1).
Expanding it reproduces the data of the entry.

The conjecture (R. J. Mathar, Nov 13 2012) reads
  Conjecture: (n+1)*a(n) - 6*n*a(n-1) + 12*(n-1)*a(n-2) - 12*a(n-3) + 8*(7-2*n)*a(n-4) = 0
It involves a(n-4) and the offset is 0, so it is stated for n >= 4.
-/

namespace OMA.S_oeis_a174016

open PowerSeries

/-- The radicand of the generating function. -/
noncomputable def R : PowerSeries ℚ := 1 - 4 * X + 4 * X ^ 2 + 8 * X ^ 3

/-- The square root of the radicand with constant term 1: (1 + X)^(1/2) evaluated at R - 1. -/
noncomputable def S : PowerSeries ℚ := (PowerSeries.binomialSeries ℚ (1 / 2 : ℚ)).subst (R - 1)

/-- A174016: the coefficient of x^n in the generating function of the entry. -/
noncomputable def a (n : ℕ) : ℚ :=
  coeff (n + 1)
    ((-1 + 4 * X + S)
      * (2 - 4 * X : PowerSeries ℚ)⁻¹)

/-- The conjectured recurrence for A174016. -/
theorem main : ∀ n : ℕ, 4 ≤ n →
    ((n : ℚ) + 1) * a n + (-6 * (n : ℚ)) * a (n - 1) + (12 * (n : ℚ) - 12) * a (n - 2)
      + (-12) * a (n - 3) + (-16 * (n : ℚ) + 56) * a (n - 4) = 0 := by
  sorry

end OMA.S_oeis_a174016

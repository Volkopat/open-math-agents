import Mathlib

/-!
# A025175: Jacobi polynomial P((1, 1), n, (1/2)).

Source: https://oeis.org/A025175
Credit: @vivanpoddar

The sequence (offset 0) begins 1, 4, 3, -40, -190, -168, 2023, 10096, 9486, ...
The entry gives the generating function
  1/(6*x^2) + (2*x-1)/(6*x^2*sqrt(16*x^2-4*x+1))
(see the entry). It is used here as the definition: a(n) is the coefficient of x^n of that series, where
the square root is the power series with constant term 1 (the binomial series (1 + X)^(1/2) evaluated
at the radicand minus 1). With R = 16*x^2 - 4*x + 1 the series is, in normalised form,
  (16*x^2 - 4*x + 1 + (2*x - 1)*sqrt(R)) / (96*x^4 - 24*x^3 + 6*x^2),
which is the expression used below (the division by x^2 is the shift of the index by 2).
Expanding it reproduces the data of the entry.

The conjecture (R. J. Mathar, Mar 03 2013) reads
  Conjecture: (n+2)*a(n) + 6*(-n-1)*a(n-1) + 12*(2*n+1)*a(n-2) + 32*(-n+1)*a(n-3) = 0
It involves a(n-3) and the offset is 0, so it is stated for n >= 3.
-/

namespace OMA.S_oeis_a025175

open PowerSeries

/-- The radicand of the generating function. -/
noncomputable def R : PowerSeries ℚ := 1 - 4 * X + 16 * X ^ 2

/-- The square root of the radicand with constant term 1: (1 + X)^(1/2) evaluated at R - 1. -/
noncomputable def S : PowerSeries ℚ := (PowerSeries.binomialSeries ℚ (1 / 2 : ℚ)).subst (R - 1)

/-- A025175: the coefficient of x^n in the generating function of the entry. -/
noncomputable def a (n : ℕ) : ℚ :=
  coeff (n + 2)
    ((1 - 4 * X + 16 * X ^ 2 + (-1 + 2 * X) * S)
      * (6 - 24 * X + 96 * X ^ 2 : PowerSeries ℚ)⁻¹)

/-- The conjectured recurrence for A025175. -/
theorem main : ∀ n : ℕ, 3 ≤ n →
    ((n : ℚ) + 2) * a n + (-6 * (n : ℚ) - 6) * a (n - 1) + (24 * (n : ℚ) + 12) * a (n - 2)
      + (-32 * (n : ℚ) + 32) * a (n - 3) = 0 := by
  sorry

end OMA.S_oeis_a025175

import Mathlib

/-!
# A115256: Diagonal sums of correlation triangle of central binomial coefficients.

Source: https://oeis.org/A115256
Credit: @vivanpoddar

The sequence (offset 0) begins 1, 2, 8, 25, 90, 312, 1145, 4186, 15640, ...
The entry gives the generating function
  1/(sqrt(1-4*x)*sqrt(1-4*x^2)*(1-x^3))
(see the entry). It is used here as the definition: a(n) is the coefficient of x^n of that series, where
the square root is the power series with constant term 1 (the binomial series (1 + X)^(1/2) evaluated
at the radicand minus 1). With R = 16*x^3 - 4*x^2 - 4*x + 1 the series is, in normalised form,
  (0 + (1)*sqrt(R)) / (-16*x^6 + 4*x^5 + 4*x^4 + 15*x^3 - 4*x^2 - 4*x + 1),
which is the expression used below (the division by x^0 is the shift of the index by 0).
Expanding it reproduces the data of the entry.

The conjecture (R. J. Mathar, Jun 22 2016) reads
  Conjecture: n*a(n) + 2*(-2*n+1)*a(n-1) + 4*(-n+1)*a(n-2) + 3*(5*n-8)*a(n-3) + 2*(2*n-1)*a(n-4) + 4*(n-1)*a(n-5) + 8*(-2*n+3)*a(n-6) = 0
It involves a(n-6) and the offset is 0, so it is stated for n >= 6.
-/

namespace OMA.S_oeis_a115256

open PowerSeries

/-- The radicand of the generating function. -/
noncomputable def R : PowerSeries ℚ := 1 - 4 * X - 4 * X ^ 2 + 16 * X ^ 3

/-- The square root of the radicand with constant term 1: (1 + X)^(1/2) evaluated at R - 1. -/
noncomputable def S : PowerSeries ℚ := (PowerSeries.binomialSeries ℚ (1 / 2 : ℚ)).subst (R - 1)

/-- A115256: the coefficient of x^n in the generating function of the entry. -/
noncomputable def a (n : ℕ) : ℚ :=
  coeff n
    ((S)
      * (1 - 4 * X - 4 * X ^ 2 + 15 * X ^ 3 + 4 * X ^ 4 + 4 * X ^ 5 - 16 * X ^ 6 : PowerSeries ℚ)⁻¹)

/-- The conjectured recurrence for A115256. -/
theorem main : ∀ n : ℕ, 6 ≤ n →
    (n : ℚ) * a n + (-4 * (n : ℚ) + 2) * a (n - 1) + (-4 * (n : ℚ) + 4) * a (n - 2)
      + (15 * (n : ℚ) - 24) * a (n - 3) + (4 * (n : ℚ) - 2) * a (n - 4)
      + (4 * (n : ℚ) - 4) * a (n - 5) + (-16 * (n : ℚ) + 24) * a (n - 6) = 0 := by
  sorry

end OMA.S_oeis_a115256

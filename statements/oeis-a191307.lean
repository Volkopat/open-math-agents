import Mathlib

/-!
# A191307: Sum of the heights of the first peaks in all dispersed Dyck paths of length n (i.e., in Motzkin paths of length n with no (1,0)-steps at positive heights).

Source: https://oeis.org/A191307
Credit: @vivanpoddar

The sequence (offset 0) begins 0, 0, 1, 2, 6, 11, 26, 47, 103, ...
The entry gives the generating function
  ((1-z-z^2)*sqrt(1-4*z^2) - (1-2*z)*(1+z-z^2))/(2*z^3*(1-z)*(1-2*z))
(see the entry). It is used here as the definition: a(n) is the coefficient of x^n of that series, where
the square root is the power series with constant term 1 (the binomial series (1 + X)^(1/2) evaluated
at the radicand minus 1). With R = 1 - 4*x^2 the series is, in normalised form,
  (-2*x^3 + 3*x^2 + x - 1 + (-x^2 - x + 1)*sqrt(R)) / (4*x^5 - 6*x^4 + 2*x^3),
which is the expression used below (the division by x^3 is the shift of the index by 3).
Expanding it reproduces the data of the entry.

The conjecture (R. J. Mathar, Jun 14 2016) reads
  Conjecture: -(n+3)*(n-2)*a(n) +(n^2+3*n-6)*a(n-1) +2*n*(2*n-3)*a(n-2) - 4*n*(n-1)*a(n-3)=0
It involves a(n-3) and the offset is 0, so it is stated for n >= 3.
-/

namespace OMA.S_oeis_a191307

open PowerSeries

/-- The radicand of the generating function. -/
noncomputable def R : PowerSeries ℚ := 1 - 4 * X ^ 2

/-- The square root of the radicand with constant term 1: (1 + X)^(1/2) evaluated at R - 1. -/
noncomputable def S : PowerSeries ℚ := (PowerSeries.binomialSeries ℚ (1 / 2 : ℚ)).subst (R - 1)

/-- A191307: the coefficient of x^n in the generating function of the entry. -/
noncomputable def a (n : ℕ) : ℚ :=
  coeff (n + 3)
    ((-1 + X + 3 * X ^ 2 - 2 * X ^ 3 + (1 - X - X ^ 2) * S)
      * (2 - 6 * X + 4 * X ^ 2 : PowerSeries ℚ)⁻¹)

/-- The conjectured recurrence for A191307. -/
theorem main : ∀ n : ℕ, 3 ≤ n →
    (-(n : ℚ) ^ 2 - (n : ℚ) + 6) * a n + ((n : ℚ) ^ 2 + 3 * (n : ℚ) - 6) * a (n - 1)
      + (4 * (n : ℚ) ^ 2 - 6 * (n : ℚ)) * a (n - 2)
      + (-4 * (n : ℚ) ^ 2 + 4 * (n : ℚ)) * a (n - 3) = 0 := by
  sorry

end OMA.S_oeis_a191307

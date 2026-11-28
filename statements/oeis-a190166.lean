import Mathlib

/-!
# A190166: Number of (1,0)-steps at levels 0,2,4,... in all peakless Motzkin paths of length n.

Source: https://oeis.org/A190166
Credit: @vivanpoddar

The sequence (offset 0) begins 0, 1, 2, 3, 6, 14, 34, 83, 202, ...
The entry gives the generating function
  z/[(1-z+z^2)sqrt((1+z+z^2)(1-3z+z^2))]
(see the entry). It is used here as the definition: a(n) is the coefficient of x^n of that series, where
the square root is the power series with constant term 1 (the binomial series (1 + X)^(1/2) evaluated
at the radicand minus 1). With R = x^4 - 2*x^3 - x^2 - 2*x + 1 the series is, in normalised form,
  (0 + (x)*sqrt(R)) / (x^6 - 3*x^5 + 2*x^4 - 3*x^3 + 2*x^2 - 3*x + 1),
which is the expression used below (the division by x^0 is the shift of the index by 0).
Expanding it reproduces the data of the entry.

The conjecture (R. J. Mathar, Apr 09 2019) reads
  Conjecture: (-n+1)*a(n) +(3*n-4)*a(n-1) +2*(-n+1)*a(n-2) +3*(n-2)*a(n-3) +2*(-n+3)*a(n-4) +(3*n-8)*a(n-5) +(-n+3)*a(n-6)=0
It involves a(n-6) and the offset is 0, so it is stated for n >= 6.
-/

namespace OMA.S_oeis_a190166

open PowerSeries

/-- The radicand of the generating function. -/
noncomputable def R : PowerSeries ℚ := 1 - 2 * X - X ^ 2 - 2 * X ^ 3 + X ^ 4

/-- The square root of the radicand with constant term 1: (1 + X)^(1/2) evaluated at R - 1. -/
noncomputable def S : PowerSeries ℚ := (PowerSeries.binomialSeries ℚ (1 / 2 : ℚ)).subst (R - 1)

/-- A190166: the coefficient of x^n in the generating function of the entry. -/
noncomputable def a (n : ℕ) : ℚ :=
  coeff n
    (((X) * S)
      * (1 - 3 * X + 2 * X ^ 2 - 3 * X ^ 3 + 2 * X ^ 4 - 3 * X ^ 5 + X ^ 6 : PowerSeries ℚ)⁻¹)

/-- The conjectured recurrence for A190166. -/
theorem main : ∀ n : ℕ, 6 ≤ n →
    (-(n : ℚ) + 1) * a n + (3 * (n : ℚ) - 4) * a (n - 1) + (-2 * (n : ℚ) + 2) * a (n - 2)
      + (3 * (n : ℚ) - 6) * a (n - 3) + (-2 * (n : ℚ) + 6) * a (n - 4)
      + (3 * (n : ℚ) - 8) * a (n - 5) + (-(n : ℚ) + 3) * a (n - 6) = 0 := by
  sorry

end OMA.S_oeis_a190166

import Mathlib

/-!
# A190169: Number of (1,0)-steps at levels 1,3,5,... in all peakless Motzkin paths of length n.

Source: https://oeis.org/A190169
Credit: @vivanpoddar

The sequence (offset 0) begins 0, 0, 0, 1, 4, 10, 24, 60, 152, ...
The entry gives the generating function
  (1-2z+z^2-2z^3+z^4)/[2z(1-z+z^2)sqrt((1+z+z^2)(1-3z+z^2))]-1/(2z)
(see the entry). It is used here as the definition: a(n) is the coefficient of x^n of that series, where
the square root is the power series with constant term 1 (the binomial series (1 + X)^(1/2) evaluated
at the radicand minus 1). With R = x^4 - 2*x^3 - x^2 - 2*x + 1 the series is, in normalised form,
  (-x^6 + 3*x^5 - 2*x^4 + 3*x^3 - 2*x^2 + 3*x - 1 + (x^4 - 2*x^3 + x^2 - 2*x + 1)*sqrt(R)) / (2*x*(x^2 - 3*x + 1)*(x^2 - x + 1)*(x^2 + x + 1)),
which is the expression used below (the division by x^1 is the shift of the index by 1).
Expanding it reproduces the data of the entry.

The conjecture (R. J. Mathar, Apr 09 2019) reads
  Conjecture: -(n-1)*(n+1)*a(n) -n*(n-19)*a(n-1) +2*(n-1)*(7*n-40)*a(n-2) -(n-2)*(17*n-97)*a(n-3) +2*(9*n^2-64*n+119)*a(n-4) -17*(n-4)*(n-5)*a(n-5) +(19*n-59)*(n-5)*a(n-6) -2*(8*n-21)*(n-6)*a(n-7) +2*(2*n-5)*(n-7)*a(n-8)=0
It involves a(n-8) and the offset is 0, so it is stated for n >= 8.
-/

namespace OMA.S_oeis_a190169

open PowerSeries

/-- The radicand of the generating function. -/
noncomputable def R : PowerSeries ℚ := 1 - 2 * X - X ^ 2 - 2 * X ^ 3 + X ^ 4

/-- The square root of the radicand with constant term 1: (1 + X)^(1/2) evaluated at R - 1. -/
noncomputable def S : PowerSeries ℚ := (PowerSeries.binomialSeries ℚ (1 / 2 : ℚ)).subst (R - 1)

/-- A190169: the coefficient of x^n in the generating function of the entry. -/
noncomputable def a (n : ℕ) : ℚ :=
  coeff (n + 1)
    ((-1 + 3 * X - 2 * X ^ 2 + 3 * X ^ 3 - 2 * X ^ 4 + 3 * X ^ 5 - X ^ 6 + (1 - 2 * X + X ^ 2 - 2 * X ^ 3 + X ^ 4) * S)
      * (2 - 6 * X + 4 * X ^ 2 - 6 * X ^ 3 + 4 * X ^ 4 - 6 * X ^ 5 + 2 * X ^ 6 : PowerSeries ℚ)⁻¹)

/-- The conjectured recurrence for A190169. -/
theorem main : ∀ n : ℕ, 8 ≤ n →
    (-(n : ℚ) ^ 2 + 1) * a n + (-(n : ℚ) ^ 2 + 19 * (n : ℚ)) * a (n - 1)
      + (14 * (n : ℚ) ^ 2 - 94 * (n : ℚ) + 80) * a (n - 2)
      + (-17 * (n : ℚ) ^ 2 + 131 * (n : ℚ) - 194) * a (n - 3)
      + (18 * (n : ℚ) ^ 2 - 128 * (n : ℚ) + 238) * a (n - 4)
      + (-17 * (n : ℚ) ^ 2 + 153 * (n : ℚ) - 340) * a (n - 5)
      + (19 * (n : ℚ) ^ 2 - 154 * (n : ℚ) + 295) * a (n - 6)
      + (-16 * (n : ℚ) ^ 2 + 138 * (n : ℚ) - 252) * a (n - 7)
      + (4 * (n : ℚ) ^ 2 - 38 * (n : ℚ) + 70) * a (n - 8) = 0 := by
  sorry

end OMA.S_oeis_a190169

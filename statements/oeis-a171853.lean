import Mathlib

/-!
# A171853: Sum of the trapezoid weights of all peakless Motzkin paths of length n (n>=0).

Source: https://oeis.org/A171853
Credit: @vivanpoddar

The sequence (offset 0) begins 0, 0, 0, 1, 3, 8, 20, 49, 119, ...
The entry gives the generating function
  z^3*g/((1 + z)*(1 - z + z^2 - 2*z^2*g)*(1 - z)^2), where g = g(z) satisfies g = 1 + z*g + z^2*g*(g - 1), that is g = (1 - z + z^2 - sqrt((1-3*z+z^2)*(1+z+z^2)))/(2*z^2)
(see the entry). It is used here as the definition: a(n) is the coefficient of x^n of that series, where
the square root is the power series with constant term 1 (the binomial series (1 + X)^(1/2) evaluated
at the radicand minus 1). With R = x^4 - 2*x^3 - x^2 - 2*x + 1 the series is, in normalised form,
  (-x^5 + 2*x^4 + x^3 + 2*x^2 - x + (x^3 - x^2 + x)*sqrt(R)) / (2*(x - 1)^2*(x + 1)*(x^2 - 3*x + 1)*(x^2 + x + 1)),
which is the expression used below (the division by x^0 is the shift of the index by 0).
Expanding it reproduces the data of the entry.

The conjecture (R. J. Mathar, Dec 07 2017) reads
  Conjecture: (-n+1)*a(n) +(3*n-5)*a(n-1) +(-n+7)*a(n-2) -7*a(n-3) -5*a(n-4) -7*a(n-5) +n*a(n-6) +(-3*n+16)*a(n-7) +(n-6)*a(n-8)=0
It involves a(n-8) and the offset is 0, so it is stated for n >= 8.
-/

namespace OMA.S_oeis_a171853

open PowerSeries

/-- The radicand of the generating function. -/
noncomputable def R : PowerSeries ℚ := 1 - 2 * X - X ^ 2 - 2 * X ^ 3 + X ^ 4

/-- The square root of the radicand with constant term 1: (1 + X)^(1/2) evaluated at R - 1. -/
noncomputable def S : PowerSeries ℚ := (PowerSeries.binomialSeries ℚ (1 / 2 : ℚ)).subst (R - 1)

/-- A171853: the coefficient of x^n in the generating function of the entry. -/
noncomputable def a (n : ℕ) : ℚ :=
  coeff n
    ((-X + 2 * X ^ 2 + X ^ 3 + 2 * X ^ 4 - X ^ 5 + (X - X ^ 2 + X ^ 3) * S)
      * (2 - 6 * X + 4 * X ^ 3 + 4 * X ^ 4 - 6 * X ^ 6 + 2 * X ^ 7 : PowerSeries ℚ)⁻¹)

/-- The conjectured recurrence for A171853. -/
theorem main : ∀ n : ℕ, 8 ≤ n →
    (-(n : ℚ) + 1) * a n + (3 * (n : ℚ) - 5) * a (n - 1) + (-(n : ℚ) + 7) * a (n - 2)
      + (-7) * a (n - 3) + (-5) * a (n - 4) + (-7) * a (n - 5) + (n : ℚ) * a (n - 6)
      + (-3 * (n : ℚ) + 16) * a (n - 7) + ((n : ℚ) - 6) * a (n - 8) = 0 := by
  sorry

end OMA.S_oeis_a171853

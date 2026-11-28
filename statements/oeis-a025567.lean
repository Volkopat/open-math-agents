import Mathlib

/-!
# A025567: a(n) = T(n,n+1), where T is the array defined in A025564.

Source: https://oeis.org/A025567
Credit: @vivanpoddar

The sequence (offset 1) begins 1, 4, 13, 40, 120, 356, 1050, 3088, 9069, ...
The entry gives the generating function
  (x^2-1-sqrt(1+x)*(x^2+2*x-1)/sqrt(1-3*x))/(2*x^3)
(Mark van Hoeij, May 01 2013). It is used here as the definition: a(n) is the coefficient of x^n of that series, where
the square root is the power series with constant term 1 (the binomial series (1 + X)^(1/2) evaluated
at the radicand minus 1). With R = -3*x^2 - 2*x + 1 the series is, in normalised form,
  (-3*x^3 + x^2 + 3*x - 1 + (-x^2 - 2*x + 1)*sqrt(R)) / (-6*x^4 + 2*x^3),
which is the expression used below (the division by x^3 is the shift of the index by 3).
Expanding it reproduces the data of the entry.

The conjecture (R. J. Mathar, Apr 03 2015) reads
  Conjecture: (n+3)*a(n) +4*(-n-2)*a(n-1) +2*a(n-2) +8*(n-1)*a(n-3) +3*(n-3)*a(n-4)=0
It involves a(n-4) and the offset is 1, so it is stated for n >= 5.
-/

namespace OMA.S_oeis_a025567

open PowerSeries

/-- The radicand of the generating function. -/
noncomputable def R : PowerSeries ℚ := 1 - 2 * X - 3 * X ^ 2

/-- The square root of the radicand with constant term 1: (1 + X)^(1/2) evaluated at R - 1. -/
noncomputable def S : PowerSeries ℚ := (PowerSeries.binomialSeries ℚ (1 / 2 : ℚ)).subst (R - 1)

/-- A025567: the coefficient of x^n in the generating function of the entry. -/
noncomputable def a (n : ℕ) : ℚ :=
  coeff (n + 3)
    ((-1 + 3 * X + X ^ 2 - 3 * X ^ 3 + (1 - 2 * X - X ^ 2) * S)
      * (2 - 6 * X : PowerSeries ℚ)⁻¹)

/-- The conjectured recurrence for A025567. -/
theorem main : ∀ n : ℕ, 5 ≤ n →
    ((n : ℚ) + 3) * a n + (-4 * (n : ℚ) - 8) * a (n - 1) + (2) * a (n - 2)
      + (8 * (n : ℚ) - 8) * a (n - 3) + (3 * (n : ℚ) - 9) * a (n - 4) = 0 := by
  sorry

end OMA.S_oeis_a025567

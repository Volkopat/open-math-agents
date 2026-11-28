import Mathlib

/-!
# A173993: Sequence whose Hankel transform is the Somos (4) sequence.

Source: https://oeis.org/A173993
Credit: @vivanpoddar

The sequence (offset 0) begins 1, 2, 6, 17, 50, 146, 430, 1267, 3746, ...
The entry gives the generating function
  (sqrt((1-2x)*(1-2x-4x^2+4x^3))-2x^2+4x-1)/(2x*(1-4x+3x^2))
(see the entry). It is used here as the definition: a(n) is the coefficient of x^n of that series, where
the square root is the power series with constant term 1 (the binomial series (1 + X)^(1/2) evaluated
at the radicand minus 1). With R = -8*x^4 + 12*x^3 - 4*x + 1 the series is, in normalised form,
  (-2*x^2 + 4*x - 1 + (1)*sqrt(R)) / (6*x^3 - 8*x^2 + 2*x),
which is the expression used below (the division by x^1 is the shift of the index by 1).
Expanding it reproduces the data of the entry.

The conjecture (R. J. Mathar, Oct 10 2014) reads
  Conjecture: (n+1)*a(n) +2*(-4*n-1)*a(n-1) +(19*n-5)*a(n-2) -36*a(n-3) +8*(-7*n+26)*a(n-4) +2*(34*n-143)*a(n-5) +24*(-n+5)*a(n-6)=0
It involves a(n-6) and the offset is 0, so it is stated for n >= 6.
-/

namespace OMA.S_oeis_a173993

open PowerSeries

/-- The radicand of the generating function. -/
noncomputable def R : PowerSeries ℚ := 1 - 4 * X + 12 * X ^ 3 - 8 * X ^ 4

/-- The square root of the radicand with constant term 1: (1 + X)^(1/2) evaluated at R - 1. -/
noncomputable def S : PowerSeries ℚ := (PowerSeries.binomialSeries ℚ (1 / 2 : ℚ)).subst (R - 1)

/-- A173993: the coefficient of x^n in the generating function of the entry. -/
noncomputable def a (n : ℕ) : ℚ :=
  coeff (n + 1)
    ((-1 + 4 * X - 2 * X ^ 2 + S)
      * (2 - 8 * X + 6 * X ^ 2 : PowerSeries ℚ)⁻¹)

/-- The conjectured recurrence for A173993. -/
theorem main : ∀ n : ℕ, 6 ≤ n →
    ((n : ℚ) + 1) * a n + (-8 * (n : ℚ) - 2) * a (n - 1) + (19 * (n : ℚ) - 5) * a (n - 2)
      + (-36) * a (n - 3) + (-56 * (n : ℚ) + 208) * a (n - 4)
      + (68 * (n : ℚ) - 286) * a (n - 5) + (-24 * (n : ℚ) + 120) * a (n - 6) = 0 := by
  sorry

end OMA.S_oeis_a173993

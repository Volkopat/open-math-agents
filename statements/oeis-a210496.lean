import Mathlib

/-!
# A210496: Number of set partitions of [n] avoiding the patterns {1123, 1211}.

Source: https://oeis.org/A210496
Credit: @vivanpoddar

The sequence (offset 0) begins 1, 1, 2, 5, 13, 33, 81, 196, 470, ...
The entry gives the generating function
  ( (1-x^2)*sqrt((1-x)*(1-x-4*x^2)) -(1-3*x-2*x^2 +14*x^3 -15*x^4 +3*x^5) / (1-x)^2 ) / ( 2*x^2*(1-3*x+x^2) )
(see the entry). It is used here as the definition: a(n) is the coefficient of x^n of that series, where
the square root is the power series with constant term 1 (the binomial series (1 + X)^(1/2) evaluated
at the radicand minus 1). With R = 4*x^3 - 3*x^2 - 2*x + 1 the series is, in normalised form,
  (-3*x^5 + 15*x^4 - 14*x^3 + 2*x^2 + 3*x - 1 + (-x^4 + 2*x^3 - 2*x + 1)*sqrt(R)) / (2*x^6 - 10*x^5 + 16*x^4 - 10*x^3 + 2*x^2),
which is the expression used below (the division by x^2 is the shift of the index by 2).
Expanding it reproduces the data of the entry.

The conjecture (R. J. Mathar, Oct 08 2016) reads
  Conjecture: (n+2)*a(n) +2*(-3*n-4)*a(n-1) +4*(2*n+3)*a(n-2) +(13*n-40)*a(n-3) +5*(-7*n+18)*a(n-4) +6*(2*n-1)*a(n-5) +22*(n-7)*a(n-6) +(-19*n+134)*a(n-7) +2*(2*n-15)*a(n-8)=0
It involves a(n-8) and the offset is 0, so it is stated for n >= 8.
-/

namespace OMA.S_oeis_a210496

open PowerSeries

/-- The radicand of the generating function. -/
noncomputable def R : PowerSeries ℚ := 1 - 2 * X - 3 * X ^ 2 + 4 * X ^ 3

/-- The square root of the radicand with constant term 1: (1 + X)^(1/2) evaluated at R - 1. -/
noncomputable def S : PowerSeries ℚ := (PowerSeries.binomialSeries ℚ (1 / 2 : ℚ)).subst (R - 1)

/-- A210496: the coefficient of x^n in the generating function of the entry. -/
noncomputable def a (n : ℕ) : ℚ :=
  coeff (n + 2)
    ((-1 + 3 * X + 2 * X ^ 2 - 14 * X ^ 3 + 15 * X ^ 4 - 3 * X ^ 5 + (1 - 2 * X + 2 * X ^ 3 - X ^ 4) * S)
      * (2 - 10 * X + 16 * X ^ 2 - 10 * X ^ 3 + 2 * X ^ 4 : PowerSeries ℚ)⁻¹)

/-- The conjectured recurrence for A210496. -/
theorem main : ∀ n : ℕ, 8 ≤ n →
    ((n : ℚ) + 2) * a n + (-6 * (n : ℚ) - 8) * a (n - 1) + (8 * (n : ℚ) + 12) * a (n - 2)
      + (13 * (n : ℚ) - 40) * a (n - 3) + (-35 * (n : ℚ) + 90) * a (n - 4)
      + (12 * (n : ℚ) - 6) * a (n - 5) + (22 * (n : ℚ) - 154) * a (n - 6)
      + (-19 * (n : ℚ) + 134) * a (n - 7) + (4 * (n : ℚ) - 30) * a (n - 8) = 0 := by
  sorry

end OMA.S_oeis_a210496

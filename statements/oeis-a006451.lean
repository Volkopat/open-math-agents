import Mathlib

/-!
# A006451: Numbers k such that k*(k+1)/2 + 1 is a square.

Source: https://oeis.org/A006451
Credit: @agchua

Formula section of A006451:
  G.f.: x*(-2-3*x+2*x^2+x^3)/(x-1)/(x^2+2*x-1)/(x^2-2*x-1). Conjectured (correctly) by
  Simon Plouffe in his 1992 dissertation.
The offset is 0 (a(0) = 0, a(1) = 2, a(2) = 5, ...), so a(n) is the n-th (from 0) natural number
k such that k(k+1)/2 + 1 is a square, Nat.nth of that predicate (k(k+1) is even, so the
division is exact). The g.f. is stated as an identity of formal power series over Q, after
multiplying by the denominator:
(sum over n >= 0 of a(n) X^n) * ((X - 1)(X^2 + 2X - 1)(X^2 - 2X - 1)) = X(-2 - 3X + 2X^2 + X^3).
-/

namespace OMA.S_oeis_a006451

/-- A006451: the n-th (from 0) natural number k such that k(k+1)/2 + 1 is a square. -/
noncomputable def a (n : ℕ) : ℕ := Nat.nth (fun k => IsSquare (k * (k + 1) / 2 + 1)) n

/-- The g.f. x(-2 - 3x + 2x^2 + x^3)/((x - 1)(x^2 + 2x - 1)(x^2 - 2x - 1)). -/
theorem main : PowerSeries.mk (fun n => (a n : ℚ)) *
      ((PowerSeries.X - 1) * (PowerSeries.X ^ 2 + 2 * PowerSeries.X - 1) *
        (PowerSeries.X ^ 2 - 2 * PowerSeries.X - 1)) =
      PowerSeries.X * (-2 - 3 * PowerSeries.X + 2 * PowerSeries.X ^ 2 + PowerSeries.X ^ 3) := by
  sorry

end OMA.S_oeis_a006451

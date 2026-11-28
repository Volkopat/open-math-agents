import Mathlib

/-!
# A021011: Pisot sequence P(6,11), a(0)=6, a(1)=11, a(n+1) is the nearest integer to a(n)^2/a(n-1).

Source: https://oeis.org/A021011
Credit: @agchua

Ralf Stephan (May 12 2004), in the formula section of A021011:
  G.f.: (3x^5+2x^4+x^3+4x^2-x+6)/(-x^6-x^3+x^2-2x+1) (conjectured).
This file states the g.f. as an identity of formal power series over ℚ (offset 0),
(∑ a(n) X^n) * (-X^6 - X^3 + X^2 - 2X + 1) = 3X^5 + 2X^4 + X^3 + 4X^2 - X + 6.
Definition: a(0) = 6, a(1) = 11, a(n+2) = ceiling(a(n+1)^2/a(n) - 1/2), with the quotient taken in ℚ and
Int.ceil. This is the definition of the Pisot sequence P(x,y) in A008776 (to which the Pisot entries
refer), a(n) = ceiling(a(n-1)^2/a(n-2) - 1/2), and the rule of the entry's PARI program and of its first
Mathematica program: the nearest integer to a(n+1)^2/a(n), with a half rounded down.
-/

namespace OMA.S_oeis_a021011

/-- A021011: a(0) = 6, a(1) = 11, a(n+2) = ceiling(a(n+1)^2/a(n) - 1/2). -/
def a : ℕ → ℤ
  | 0 => 6
  | 1 => 11
  | (n + 2) => ⌈((a (n + 1) : ℚ) ^ 2 / (a n : ℚ)) - 1 / 2⌉

/-- Ralf Stephan's conjectured g.f. (3x^5+2x^4+x^3+4x^2-x+6)/(-x^6-x^3+x^2-2x+1). -/
theorem main : PowerSeries.mk (fun n => (a n : ℚ)) *
      (-PowerSeries.X ^ 6 - PowerSeries.X ^ 3 + PowerSeries.X ^ 2 - 2 * PowerSeries.X + 1) =
    3 * PowerSeries.X ^ 5 + 2 * PowerSeries.X ^ 4 + PowerSeries.X ^ 3 + 4 * PowerSeries.X ^ 2 -
      PowerSeries.X + 6 := by
  sorry

end OMA.S_oeis_a021011

import Mathlib

/-!
# A021008: Pisot sequence P(5,11), a(0)=5, a(1)=11, a(n+1) is the nearest integer to a(n)^2/a(n-1).

Source: https://oeis.org/A021008
Credit: @agchua

Two conjectures in the formula section of A021008:
  Conjecture: G.f.: (2x^3+x^2-4x+5)/(-x^4+2x^2-3x+1). - Ralf Stephan, May 12 2004
  Conjecture: a(0)=5, a(1)=11, a(2)=24, a(3)=52, a(n)=3*a(n-1)-2*a(n-2)+a(n-4). - Harvey P. Dale,
  May 19 2015
This file states both: the recurrence for n ≥ 4 (offset 0, so that all indices are terms; the initial
values a(2) = 24 and a(3) = 52 are also fixed by the g.f.), and the g.f. as an identity of formal power
series over ℚ, (∑ a(n) X^n) * (-X^4 + 2X^2 - 3X + 1) = 2X^3 + X^2 - 4X + 5.
Definition: a(0) = 5, a(1) = 11, a(n+2) = ceiling(a(n+1)^2/a(n) - 1/2), with the quotient taken in ℚ and
Int.ceil. This is the definition of the Pisot sequence P(x,y) in A008776 (to which the Pisot entries
refer), a(n) = ceiling(a(n-1)^2/a(n-2) - 1/2), and the rule of the entry's PARI program and of its second
Mathematica program: the nearest integer to a(n+1)^2/a(n), with a half rounded down.
-/

namespace OMA.S_oeis_a021008

/-- A021008: a(0) = 5, a(1) = 11, a(n+2) = ceiling(a(n+1)^2/a(n) - 1/2). -/
def a : ℕ → ℤ
  | 0 => 5
  | 1 => 11
  | (n + 2) => ⌈((a (n + 1) : ℚ) ^ 2 / (a n : ℚ)) - 1 / 2⌉

/-- The conjectures of Harvey P. Dale and Ralf Stephan: a(n) = 3a(n-1) - 2a(n-2) + a(n-4) for n ≥ 4,
and the g.f. (2x^3+x^2-4x+5)/(-x^4+2x^2-3x+1). -/
theorem main : (∀ n : ℕ, 4 ≤ n → a n = 3 * a (n - 1) - 2 * a (n - 2) + a (n - 4)) ∧
    PowerSeries.mk (fun n => (a n : ℚ)) *
        (-PowerSeries.X ^ 4 + 2 * PowerSeries.X ^ 2 - 3 * PowerSeries.X + 1) =
      2 * PowerSeries.X ^ 3 + PowerSeries.X ^ 2 - 4 * PowerSeries.X + 5 := by
  sorry

end OMA.S_oeis_a021008

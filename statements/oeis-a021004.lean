import Mathlib

/-!
# A021004: Pisot sequence P(4,10).

Source: https://oeis.org/A021004
Credit: @agchua

Two conjectures in the formula section of A021004:
  Conjecture: a(n) = 2a(n-1) + a(n-2) + a(n-3) - a(n-4) - a(n-6) (checked up to n = 1000)
  Conjectured G.f.: (4+2 x+x^2-2 x^3-x^4-2 x^5)/(1-2 x-x^2-x^3+ x^4+x^6) - Harvey P. Dale, Mar 12 2011
This file states both: the recurrence for n ≥ 6 (offset 0, so that all indices are terms), and the
g.f. as an identity of formal power series over ℚ,
(∑ a(n) X^n) * (1 - 2X - X^2 - X^3 + X^4 + X^6) = 4 + 2X + X^2 - 2X^3 - X^4 - 2X^5.
Definition: a(0) = 4, a(1) = 10, a(n+2) = ceiling(a(n+1)^2/a(n) - 1/2), with the quotient taken in ℚ and
Int.ceil. This is the definition of the Pisot sequence P(x,y) in A008776, to which the entry refers
(a(n) = ceiling(a(n-1)^2/a(n-2) - 1/2)), and the rule of the entry's Mathematica and PARI programs. It
matters here: 25^2/10 = 62.5, and the listed a(3) = 62 is this rule (a half is rounded down).
-/

namespace OMA.S_oeis_a021004

/-- A021004: a(0) = 4, a(1) = 10, a(n+2) = ceiling(a(n+1)^2/a(n) - 1/2). -/
def a : ℕ → ℤ
  | 0 => 4
  | 1 => 10
  | (n + 2) => ⌈((a (n + 1) : ℚ) ^ 2 / (a n : ℚ)) - 1 / 2⌉

/-- The conjectured recurrence a(n) = 2a(n-1) + a(n-2) + a(n-3) - a(n-4) - a(n-6) for n ≥ 6, and
Harvey P. Dale's conjectured g.f. (4+2x+x^2-2x^3-x^4-2x^5)/(1-2x-x^2-x^3+x^4+x^6). -/
theorem main : (∀ n : ℕ, 6 ≤ n →
      a n = 2 * a (n - 1) + a (n - 2) + a (n - 3) - a (n - 4) - a (n - 6)) ∧
    PowerSeries.mk (fun n => (a n : ℚ)) *
        (1 - 2 * PowerSeries.X - PowerSeries.X ^ 2 - PowerSeries.X ^ 3 + PowerSeries.X ^ 4 +
          PowerSeries.X ^ 6) =
      4 + 2 * PowerSeries.X + PowerSeries.X ^ 2 - 2 * PowerSeries.X ^ 3 - PowerSeries.X ^ 4 -
        2 * PowerSeries.X ^ 5 := by
  sorry

end OMA.S_oeis_a021004

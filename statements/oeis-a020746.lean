import Mathlib

/-!
# A020746: Pisot sequence T(3,7), a(n) = floor(a(n-1)^2/a(n-2)).

Source: https://oeis.org/A020746
Credit: @agchua

Ralf Stephan (May 12 2004), in the formula section of A020746:
  Conjectured g.f.: (-x^5+x^4-x^3+x^2-2*x+3)/((1-x)*(1-2*x-x^3-x^5)).
The entry adds: I believe that David Boyd has proved that this g.f. is correct. - N. J. A. Sloane,
Aug 11 2016; no proof is given in the entry.
This file states the g.f. as an identity of formal power series over ℚ,
(∑ a(n) X^n) * ((1 - X) * (1 - 2X - X^3 - X^5)) = -X^5 + X^4 - X^3 + X^2 - 2X + 3 (offset 0).
Definition: a(0) = 3, a(1) = 7, a(n+2) = floor(a(n+1)^2/a(n)), with the quotient taken in ℚ and
Int.floor: the rule in the name of the entry, of the definition of T(x,y) in A008776, and of the
entry's Mathematica, Magma and PARI programs.
-/

namespace OMA.S_oeis_a020746

/-- A020746: a(0) = 3, a(1) = 7, a(n+2) = floor(a(n+1)^2/a(n)). -/
def a : ℕ → ℤ
  | 0 => 3
  | 1 => 7
  | (n + 2) => ⌊((a (n + 1) : ℚ) ^ 2 / (a n : ℚ))⌋

/-- Ralf Stephan's conjectured g.f. (-x^5+x^4-x^3+x^2-2x+3)/((1-x)(1-2x-x^3-x^5)). -/
theorem main : PowerSeries.mk (fun n => (a n : ℚ)) *
      ((1 - PowerSeries.X) * (1 - 2 * PowerSeries.X - PowerSeries.X ^ 3 - PowerSeries.X ^ 5)) =
    -PowerSeries.X ^ 5 + PowerSeries.X ^ 4 - PowerSeries.X ^ 3 + PowerSeries.X ^ 2 -
      2 * PowerSeries.X + 3 := by
  sorry

end OMA.S_oeis_a020746

import Mathlib

/-!
# A045626: Bends in loxodromic sequence of spheres in which each 5 consecutive spheres are in mutual contact.

Source: https://oeis.org/A045626
Credit: @agchua

Ralf Stephan (May 06 2004), in the formula section of A045626:
  G.f.: -(1-3*x-2*x^2+x^3+2*x^4)/((1+x)*(1-2*x+x^2-2*x^3+x^4)) (conjectured).
This file states the g.f. as an identity of formal power series over ℚ,
(∑ a(n) X^n) * ((1 + X) * (1 - 2X + X^2 - 2X^3 + X^4)) = -(1 - 3X - 2X^2 + X^3 + 2X^4).
The sequence has offset 0. Definition: a(0) = -1, a(1) = 2, a(2) = 3, a(3) = 3, a(4) = 5 and
a(n) = a(n-1) + a(n-2) + a(n-3) + a(n-4) - a(n-5) for n ≥ 5. This is the rule of every program in
the entry (Maple, Mathematica, PARI, Magma, Sage, GAP) and it is what the geometry gives: for five
mutually tangent spheres the Soddy-Gosset relation (b1 + ... + b5)^2 = 3 (b1^2 + ... + b5^2) is
quadratic in b5 with root sum b1 + b2 + b3 + b4, so the two spheres touching four consecutive ones
have bends a(n) and a(n-5) with a(n) + a(n-5) = a(n-1) + a(n-2) + a(n-3) + a(n-4).
-/

namespace OMA.S_oeis_a045626

/-- A045626: a(0..4) = -1, 2, 3, 3, 5 and a(n+5) = a(n+4) + a(n+3) + a(n+2) + a(n+1) - a(n). -/
def a : ℕ → ℤ
  | 0 => -1
  | 1 => 2
  | 2 => 3
  | 3 => 3
  | 4 => 5
  | (n + 5) => a (n + 4) + a (n + 3) + a (n + 2) + a (n + 1) - a n

/-- Stephan's conjecture: the g.f. is -(1-3x-2x^2+x^3+2x^4)/((1+x)(1-2x+x^2-2x^3+x^4)). -/
theorem main : PowerSeries.mk (fun n => (a n : ℚ)) *
    ((1 + PowerSeries.X) * (1 - 2 * PowerSeries.X + PowerSeries.X ^ 2 - 2 * PowerSeries.X ^ 3 +
      PowerSeries.X ^ 4)) =
    -(1 - 3 * PowerSeries.X - 2 * PowerSeries.X ^ 2 + PowerSeries.X ^ 3 + 2 * PowerSeries.X ^ 4) := by
  sorry

end OMA.S_oeis_a045626

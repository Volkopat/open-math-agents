import Mathlib

/-!
# A063140: a conjectured exponential generating function

Source: https://oeis.org/A063140
Credit: @ivillar

Status: recorded in the entry as a conjecture; no proof or verification is noted there. It follows
from the formula recorded in the entry, which is used as the definition here.

A063140 (offset 1): dimension of the space of weight 2n cusp forms for Gamma_0( 72 );
data 5, 28, 52, 76, 100, 124, 148, 172, 196, 220, 244, 268, ...

Conjecture (Stefano Spezia, Mar 02 2025): e.g.f.: 20 + x + 4*exp(x)*(6*x - 5).

Formalization: the entry records a(n) = 24*n-20 for n>1 (Colin Barker, Sep 23 2012), and a(1) = 5 is
the first term; these values, in ℤ, are the definition of a(n) used here. The sequence has offset 1
and the conjectured e.g.f. has constant term 20 - 20 = 0, so a(0) = 0 is used for the coefficient of
x^0. The conjecture is stated as the identity
Sum_n a(n) x^n / n! = 20 + x + 4*exp(x)*(6*x - 5) of formal power series over ℚ.
-/

namespace OMA.S_oeis_a063140

open PowerSeries

/-- a(1) = 5 and a(n) = 24n - 20 for n > 1, the formula recorded in the entry; a(0) = 0. -/
def a (n : ℕ) : ℤ := if n = 0 then 0 else if n = 1 then 5 else 24 * (n : ℤ) - 20

/-- The conjectured exponential generating function of A063140. -/
theorem main : PowerSeries.mk (fun n => (a n : ℚ) / (n.factorial : ℚ)) =
    20 + X + 4 * PowerSeries.exp ℚ * (6 * X - 5) := by
  sorry

end OMA.S_oeis_a063140

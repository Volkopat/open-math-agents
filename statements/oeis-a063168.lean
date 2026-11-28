import Mathlib

/-!
# A063168: a conjectured recurrence and generating function

Source: https://oeis.org/A063168
Credit: @ivillar

Status: recorded in the entry as conjectures; no proof or verification is noted there. Both
statements follow from the formula recorded in the entry, which is used as the definition here.

A063168 (offset 1): dimension of the space of weight 2n cusp forms for Gamma_0( 100 );
data 7, 36, 66, 96, 126, 156, 186, 216, 246, 276, 306, 336, ...

Conjectures (Chai Wah Wu, Jun 15 2016):
(1) a(n) = 2*a(n-1) - a(n-2) for n > 3.
(2) G.f.: x*(x^2 + 22*x + 7)/(x - 1)^2.

Formalization: the entry records a(n) = a(n-1) + 30 for n > 2 (Bill McEachen, Jun 16 2025); with the
terms a(1) = 7 and a(2) = 36 this is a(n) = 30*n - 24 for n ≥ 2, and these values, in ℤ, are the
definition of a(n) used here. The sequence has offset 1 and the conjectured g.f. has no constant term,
so a(0) = 0 is used for the coefficient of x^0. The g.f. conjecture is stated as the identity
(Sum_n a(n) x^n) * (1 - x)^2 = x*(x^2 + 22*x + 7) of formal power series over ℚ (note (x-1)^2 = (1-x)^2).
`main` is the conjunction of (1) and (2).
-/

namespace OMA.S_oeis_a063168

open PowerSeries

/-- a(1) = 7 and a(n) = 30n - 24 for n ≥ 2 (that is a(2) = 36 and a(n) = a(n-1) + 30 for n > 2);
a(0) = 0. -/
def a (n : ℕ) : ℤ := if n = 0 then 0 else if n = 1 then 7 else 30 * (n : ℤ) - 24

/-- The conjectured recurrence and generating function of A063168. -/
theorem main :
    (∀ n : ℕ, 3 < n → a n = 2 * a (n - 1) - a (n - 2)) ∧
    (PowerSeries.mk (fun n => (a n : ℚ)) * (1 - X) ^ 2 = X * (X ^ 2 + 22 * X + 7)) := by
  sorry

end OMA.S_oeis_a063168

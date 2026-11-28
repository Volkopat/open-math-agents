import Mathlib

/-!
# OEIS A089640: Wu's recurrence and generating function for the partial sums of 1 + [1,2] + [2,3] + ...

Source: https://oeis.org/A089640 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry (Jon Perry, Jan 01 2004), offset 1: Enumeration of partial sums of
1 + [1,2] + [2,3] + [1,2] + [2,3] + .... Example: a(6) = 4 because we have 6 = 1+1+2+2 = 1+2+3 =
1+2+2+1 = 1+1+3+1. The formula section states: Conjectures from Chai Wah Wu, Jan 13 2023:
a(n) = a(n-3) + 2*a(n-4) + a(n-5) for n > 5. G.f.: x*(-x^2 - x - 1)/(x^5 + 2*x^4 + x^3 - 1).

Formalization notes:
* A partial sum is 1 + x_1 + ... + x_m with m >= 0, where x_1, x_3, ... lie in [1,2] = {1, 2}
  and x_2, x_4, ... lie in [2,3] = {2, 3}, as in the example; a(n) counts the sequences
  (x_1, ..., x_m) for which it equals n.
* `ways r b` counts the sequences with sum r whose terms alternate between [1,2] and [2,3],
  starting in [1,2] when b is true and in [2,3] when b is false; it is defined by splitting off
  the first term (or taking the empty sequence when r = 0). Then a(n) = ways (n - 1) true.
* `main` is the conjunction of both conjectures: the recurrence for every n > 5, and the
  generating function, stated as the identity A(x) (x^5 + 2x^4 + x^3 - 1) = x (-x^2 - x - 1)
  in Z[[x]] with A(x) = Sum_{n >= 1} a(n) x^n; x^5 + 2x^4 + x^3 - 1 is invertible in Z[[x]], so
  this is the stated quotient.
* Controls proved in the proof file: a(1..22) = 1, 1, 1, 1, 3, 4, 4, 6, 11, 15, 18, 27, 43, 59,
  78, 115, 172, 239, 330, 480, 698, 980, the entry's data.
-/

namespace OMA.S_oeis_a089640

/-- `ways r b`: the number of finite sequences x_1, x_2, ... (possibly empty) with sum r whose
terms alternate between [1,2] and [2,3], the first term in [1,2] when `b` is true and in [2,3]
when `b` is false. -/
def ways : ℕ → Bool → ℕ
  | 0, _ => 1
  | 1, true => 1
  | 1, false => 0
  | 2, true => ways 1 false + ways 0 false
  | 2, false => ways 0 true
  | r + 3, true => ways (r + 2) false + ways (r + 1) false
  | r + 3, false => ways (r + 1) true + ways r true

/-- A089640(n), n >= 1: the number of ways in which a partial sum of
1 + [1,2] + [2,3] + [1,2] + ... equals n. -/
def a (n : ℕ) : ℕ := ways (n - 1) true

open PowerSeries in
/-- Wu's conjectures: the recurrence for n > 5 and the generating function. -/
theorem main :
    (∀ n : ℕ, 5 < n → a n = a (n - 3) + 2 * a (n - 4) + a (n - 5)) ∧
      PowerSeries.mk (fun n => if n = 0 then (0 : ℤ) else a n) * (X ^ 5 + 2 * X ^ 4 + X ^ 3 - 1) =
        X * (-X ^ 2 - X - 1) := by
  sorry

end OMA.S_oeis_a089640

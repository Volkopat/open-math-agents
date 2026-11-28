import Mathlib

/-!
# A335756: two conjectured formulas

Source: https://oeis.org/A335756
Credit: @ivillar

Status: recorded in the entry as conjectures; no proof or verification is noted there. Both
statements follow from the closed form recorded in the entry, which is used as the definition here.

A335756 (offset 0): a cup filling problem starting with 2 empty cups of sizes 3 and n, where a(n) is
the number of unreachable states;
data 2, 0, 2, 12, 6, 8, 22, 12, 14, 32, 18, 20, 42, 24, 26, 52, 30, 32, 62, 36, 38, 72, 42, 44, ...

Conjectures from Colin Barker, Jun 21 2020:
(1) G.f.: 2*(1 + x^2 + 4*x^3 + 3*x^4 + 2*x^5) / ((1 - x)^2*(1 + x + x^2)^2).
(2) a(n) = 2*a(n-3) - a(n-6) for n > 5.

Formalization: the entry records the closed form
a(n) = 2*(n-1)*sign(n mod 3) + (10*floor(n/3)+2)*(1-sign(n mod 3)). Since sign(n mod 3) is 0 when 3
divides n and 1 otherwise, this is a(n) = 10*floor(n/3) + 2 if 3 divides n and a(n) = 2*(n-1)
otherwise, and this is the definition of a(n) used here (with values in ℤ). The g.f. conjecture is
stated as the identity
(Sum_n a(n) x^n) * (1 - x)^2 * (1 + x + x^2)^2 = 2*(1 + x^2 + 4*x^3 + 3*x^4 + 2*x^5)
of formal power series over ℚ. `main` is the conjunction of (1) and (2).
-/

namespace OMA.S_oeis_a335756

open PowerSeries

/-- a(n) = 10*floor(n/3) + 2 if 3 divides n, and a(n) = 2*(n-1) otherwise. -/
def a (n : ℕ) : ℤ := if n % 3 = 0 then 10 * ((n / 3 : ℕ) : ℤ) + 2 else 2 * ((n : ℤ) - 1)

/-- The two conjectures of Colin Barker for A335756. -/
theorem main :
    (PowerSeries.mk (fun n => (a n : ℚ)) * ((1 - X) ^ 2 * (1 + X + X ^ 2) ^ 2) =
      2 * (1 + X ^ 2 + 4 * X ^ 3 + 3 * X ^ 4 + 2 * X ^ 5)) ∧
    (∀ n : ℕ, 5 < n → a n = 2 * a (n - 3) - a (n - 6)) := by
  sorry

end OMA.S_oeis_a335756

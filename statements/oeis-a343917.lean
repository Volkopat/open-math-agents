import Mathlib

/-!
# A343917: Positive integers m with 2*m^2 - 2^4 = x^4 + y^4 for some nonnegative integers x and y with |x-y| > 2.

Source: https://oeis.org/A343917
Credit: @luciusacarr

Data: 284, 1388, 2139, 4772, 8556, 8971, 10836, 21163, 28847, 45707, ...

Conjecture (from the entry): the sequence has infinitely many terms. `main` states it.

Reading of the source:
* `m` is a positive integer and `x, y` are nonnegative integers; the equation
  `2m^2 - 2^4 = x^4 + y^4` and the condition `|x - y| > 2` are stated in ℤ.
  Example: 2 * 284^2 - 2^4 = 20^4 + 6^4 with |20 - 6| > 2.
-/

namespace OMA.S_oeis_a343917

/-- The terms of A343917. -/
def S : Set ℕ :=
  {m | 0 < m ∧ ∃ x y : ℕ, 2 * (m : ℤ) ^ 2 - 2 ^ 4 = (x : ℤ) ^ 4 + (y : ℤ) ^ 4 ∧ 2 < |(x : ℤ) - y|}

theorem main :
    -- The sequence has infinitely many terms.
    S.Infinite := by
  sorry

end OMA.S_oeis_a343917

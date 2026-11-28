import Mathlib

/-!
# A343913: Positive integers m such that 2*m^2 - 1 = x^4 + y^4 for some nonnegative integers x and y with |x - y| > 1.

Source: https://oeis.org/A343913
Credit: @luciusacarr

Data: 71, 347, 1193, 2139, 2709, 17823, 18337, 26057, 32847, 34037, ...

Conjecture (from the entry): the sequence has infinitely many terms. `main` states it.

Reading of the source:
* `m` is a positive integer and `x, y` are nonnegative integers; the equation
  `2m^2 - 1 = x^4 + y^4` and the condition `|x - y| > 1` are stated in ℤ.
  Example: 2 * 71^2 - 1 = 10^4 + 3^4 with |10 - 3| > 1.
-/

namespace OMA.S_oeis_a343913

/-- The terms of A343913. -/
def S : Set ℕ :=
  {m | 0 < m ∧ ∃ x y : ℕ, 2 * (m : ℤ) ^ 2 - 1 = (x : ℤ) ^ 4 + (y : ℤ) ^ 4 ∧ 1 < |(x : ℤ) - y|}

theorem main :
    -- The sequence has infinitely many terms.
    S.Infinite := by
  sorry

end OMA.S_oeis_a343913

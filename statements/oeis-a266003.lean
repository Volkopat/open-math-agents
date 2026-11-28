import Mathlib

/-!
# A266003: Least nonnegative integer y such that n = x^4 - y^3 + z^2 for some nonnegative integers x and z, or -1 if no such y exists.

Source: https://oeis.org/A266003
Credit: @azmiozgen

Conjecture (Zhi-Wei Sun, from the entry): any integer m can be written as x^4 - y^3 + z^2, where x, y and z are nonnegative integers.

Formalization notes:
* m ranges over ℤ; x, y, z are natural numbers.
* Controls: the entry's terms begin 0, 0, 0, 1, 0, 0, 139, 19, 1, 0, 0, 9 (offset 0); the author reports a check for |m| ≤ 10^5.
-/

namespace OMA.S_oeis_a266003



/-- The conjecture of the entry. -/
theorem main :
    ∀ m : ℤ, ∃ x y z : ℕ, (x : ℤ) ^ 4 - (y : ℤ) ^ 3 + (z : ℤ) ^ 2 = m := by
  sorry

end OMA.S_oeis_a266003

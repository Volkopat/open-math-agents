import Mathlib

/-!
# A266152: Least positive integer y such that n = x^4 - y^3 + z^2 for some positive integers x and z, or 0 if no such y exists.

Source: https://oeis.org/A266152
Credit: @azmiozgen

Conjecture (Zhi-Wei Sun, from the entry): any integer m can be written as x^4 - y^3 + z^2, where x, y and z are positive integers.

Formalization notes:
* m ranges over ℤ; x, y, z are natural numbers that are positive.
* Controls: the entry's terms begin 8, 1, 2, 17, 1, 3, 139, 19, 37, 1, 3, 9 (offset 0); the author reports a check for |m| ≤ 10^5.
-/

namespace OMA.S_oeis_a266152



/-- The conjecture of the entry. -/
theorem main :
    ∀ m : ℤ, ∃ x y z : ℕ, 0 < x ∧ 0 < y ∧ 0 < z ∧ (x : ℤ) ^ 4 - (y : ℤ) ^ 3 + (z : ℤ) ^ 2 = m := by
  sorry

end OMA.S_oeis_a266152

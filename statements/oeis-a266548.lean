import Mathlib

/-!
# A266548: Least prime p such that n + p^3 = x^2 + y^3 for some positive integers x and y, or 0 if no such prime p exists.

Source: https://oeis.org/A266548
Credit: @azmiozgen

Conjecture (Zhi-Wei Sun, from the entry):
(i) Any integer can be written as x^2 + y^3 - p^3, where x and y are positive integers, and p is a
prime.
(ii) Each integer can be written as x^2 - y^3 + p^3, where x and y are positive integers, and p is a
prime.

Formalization notes:
* m ranges over ℤ; x, y are positive integers and p is prime.
* Controls: the entry's terms begin 71, 2, 2, 5, 2, 3767, 3, 7 (offset 0).
-/

namespace OMA.S_oeis_a266548



/-- The conjecture of the entry. -/
theorem main :
    (∀ m : ℤ, ∃ x y p : ℕ, 0 < x ∧ 0 < y ∧ p.Prime ∧ (x : ℤ) ^ 2 + (y : ℤ) ^ 3 - (p : ℤ) ^ 3 = m) ∧
      ∀ m : ℤ, ∃ x y p : ℕ, 0 < x ∧ 0 < y ∧ p.Prime ∧ (x : ℤ) ^ 2 - (y : ℤ) ^ 3 + (p : ℤ) ^ 3 = m := by
  sorry

end OMA.S_oeis_a266548

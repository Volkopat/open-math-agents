import Mathlib

/-!
# A283170: Number of ways to write n as x^2 + y^2 + z^2 + w^2 with x + 2*y and z + 2*w both squares, where x and w are nonnegative integers, and y and z are integers.

Source: https://oeis.org/A283170
Credit: @azmiozgen

Conjectures (Zhi-Wei Sun, from the entry):
(i) a(n) > 0 for all n = 0, 1, 2, ....
(ii) Any nonnegative integer n can be written as x^2 + y^2 + z^2 + w^2 with x + 3*y and z + 3*w
both squares, where x, y, z are integers and w is a nonnegative integer.
(iii) Every nonnegative integer can be expressed as x^2 + y^2 + z^2 + w^2 with x, y, z, w integers
such that both x + 2*y and z + 3*w are squares.

Formalization notes:
* Variables are integers (ℤ) with the stated sign conditions; "is a square" is `IsSquare` in ℤ.
* Controls (computed, |x|,|y|,|z|,|w| ≤ 40): all three parts hold for n < 1500.
-/

namespace OMA.S_oeis_a283170



/-- The conjecture of the entry (the parts listed above). -/
theorem main :
    (∀ n : ℕ, ∃ x y z w : ℤ, 0 ≤ x ∧ 0 ≤ w ∧ IsSquare (x + 2 * y) ∧ IsSquare (z + 2 * w) ∧
        x ^ 2 + y ^ 2 + z ^ 2 + w ^ 2 = n) ∧
      (∀ n : ℕ, ∃ x y z w : ℤ, 0 ≤ w ∧ IsSquare (x + 3 * y) ∧ IsSquare (z + 3 * w) ∧
        x ^ 2 + y ^ 2 + z ^ 2 + w ^ 2 = n) ∧
      ∀ n : ℕ, ∃ x y z w : ℤ, IsSquare (x + 2 * y) ∧ IsSquare (z + 3 * w) ∧
        x ^ 2 + y ^ 2 + z ^ 2 + w ^ 2 = n := by
  sorry

end OMA.S_oeis_a283170

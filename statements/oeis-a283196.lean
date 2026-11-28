import Mathlib

/-!
# A283196: Number of ways to write n as x^2 + y^2 + z^2 + w^2 with 2*x + y and 2*x + z both squares, where x,y,z are integers with |y| <= |z|, and w is a positive integer.

Source: https://oeis.org/A283196
Credit: @azmiozgen

Conjecture (Zhi-Wei Sun, from the entry):
(i) a(n) > 0 for all n > 0.
(ii) Any positive integer n can be written as x^2 + y^2 + z^2 + w^2 such that both x + y and x + 2*z
are squares, where x, y, z, w are integers with x >= 0 and w > 0.

Formalization notes:
* a(n) > 0 is stated as the existence of a representation.
* Variables are integers; "is a square" is `IsSquare` in ℤ.
* Controls (computed): both parts hold for 1 ≤ n < 800.
-/

namespace OMA.S_oeis_a283196

/-- The conjecture of the entry. -/
theorem main :
    (∀ n : ℕ, 0 < n → ∃ x y z w : ℤ, 0 < w ∧ |y| ≤ |z| ∧ IsSquare (2 * x + y) ∧ IsSquare (2 * x + z) ∧
        x ^ 2 + y ^ 2 + z ^ 2 + w ^ 2 = n) ∧
      ∀ n : ℕ, 0 < n → ∃ x y z w : ℤ, 0 ≤ x ∧ 0 < w ∧ IsSquare (x + y) ∧ IsSquare (x + 2 * z) ∧
        x ^ 2 + y ^ 2 + z ^ 2 + w ^ 2 = n := by
  sorry

end OMA.S_oeis_a283196

import Mathlib

/-!
# A300844: Number of ways to write n as x^2 + y^2 + z^2 + w^2 with x,y,z,w nonnegative integers such that x or 2*y or z is a square and (12*x)^2 + (21*y)^2 + (28*z)^2 is also a square.

Source: https://oeis.org/A300844
Credit: @azmiozgen

Conjectures (Zhi-Wei Sun, from the entry):
1. a(n) > 0 for all n = 0, 1, 2, ....
2. Any positive integer can be written as x^2 + y^2 + z^2 + w^2 with w a positive integer and x, y, z
   nonnegative integers such that x or y or z is a square and 144*x^2 + 505*y^2 + 720*z^2 is also a
   square.

Formalization notes:
* a(n) > 0 is stated as the existence of a representation.
* Controls (computed): both conjectures hold for n < 2500.
-/

namespace OMA.S_oeis_a300844

/-- Both conjectures of the entry. -/
theorem main :
    (∀ n : ℕ, ∃ x y z w : ℕ, x ^ 2 + y ^ 2 + z ^ 2 + w ^ 2 = n ∧
        (IsSquare x ∨ IsSquare (2 * y) ∨ IsSquare z) ∧
        IsSquare ((12 * x) ^ 2 + (21 * y) ^ 2 + (28 * z) ^ 2)) ∧
      ∀ n : ℕ, 0 < n → ∃ x y z w : ℕ, 0 < w ∧ x ^ 2 + y ^ 2 + z ^ 2 + w ^ 2 = n ∧
        (IsSquare x ∨ IsSquare y ∨ IsSquare z) ∧ IsSquare (144 * x ^ 2 + 505 * y ^ 2 + 720 * z ^ 2) := by
  sorry

end OMA.S_oeis_a300844

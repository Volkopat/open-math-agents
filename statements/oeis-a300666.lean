import Mathlib

/-!
# A300666: Number of ways to write n as x^2 + y^2 + z^2 + w^2 with nonnegative integers x,y,z,w and z <= w such that x or 2*y is a square and x + 3*y is also a square.

Source: https://oeis.org/A300666
Credit: @azmiozgen

Conjectures (Zhi-Wei Sun, from the entry):
1. a(n) > 0 for all n = 0, 1, 2, ....
2. Any nonnegative integer n not equal to 3 can be written as x^2 + y^2 + z^2 + w^2 with
   nonnegative integers x, y, z, w such that x or 2*y is a square and 3*x - y is also a square.

Formalization notes:
* a(n) > 0 is stated as the existence of a representation with z ≤ w.
* In conjecture 2, 3x - y is computed in ℤ; being a square means it equals s^2 for an integer s.
* Controls (computed): conjecture 1 holds for n < 2500; conjecture 2 holds for n < 2500 except
  n = 3.
-/

namespace OMA.S_oeis_a300666



/-- The conjecture of the entry (the parts listed above). -/
theorem main :
    (∀ n : ℕ, ∃ x y z w : ℕ, z ≤ w ∧ (IsSquare x ∨ IsSquare (2 * y)) ∧ IsSquare (x + 3 * y) ∧
        x ^ 2 + y ^ 2 + z ^ 2 + w ^ 2 = n) ∧
      ∀ n : ℕ, n ≠ 3 → ∃ x y z w : ℕ, (IsSquare x ∨ IsSquare (2 * y)) ∧
        (∃ s : ℤ, 3 * (x : ℤ) - y = s ^ 2) ∧ x ^ 2 + y ^ 2 + z ^ 2 + w ^ 2 = n := by
  sorry

end OMA.S_oeis_a300666

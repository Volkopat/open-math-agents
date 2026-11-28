import Mathlib

/-!
# A290342: Number of ways to write n as x^2 + 2*y^2 + z*(z+1)/2, where x is a nonnegative integer, and y and z are positive integers.

Source: https://oeis.org/A290342
Credit: @azmiozgen

Conjecture (Zhi-Wei Sun, from the entry): a(n) > 0 for all n > 2. In other words, each
n = 0, 1, 2, ... can be written as x^2 + 2y*(y+2) + z*(z+3)/2 with x, y, z nonnegative integers.

Formalization notes:
* a(n) > 0 is stated as the existence of x ≥ 0, y > 0, z > 0 with x^2 + 2y^2 + z(z+1)/2 = n.
* Controls (computed): every n with 2 < n < 6000 is represented.
-/

namespace OMA.S_oeis_a290342



/-- The conjecture of the entry (the parts listed above). -/
theorem main :
    ∀ n : ℕ, 2 < n → ∃ x y z : ℕ, 0 < y ∧ 0 < z ∧ x ^ 2 + 2 * y ^ 2 + z * (z + 1) / 2 = n := by
  sorry

end OMA.S_oeis_a290342

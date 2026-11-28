import Mathlib

/-!
# A284343: Number of ways to write n as x^2 + y^2 + z^2 + w^2 with x,y,z,w nonnegative integers and y <= z such that 2*x + y - z is either zero or a power of 8 (including 8^0 = 1).

Source: https://oeis.org/A284343
Credit: @azmiozgen

Conjecture (Zhi-Wei Sun, from the entry), part (i): for any c = 1, 2, 4, each n = 0, 1, 2, ... can be
written as x^2 + y^2 + z^2 + w^2 with x, y, z, w nonnegative integers and y <= z such that
c*(2*x+y-z) is either zero or a power of eight (including 8^0 = 1). (Part (ii), a list of further
polynomials with powers of four, is not stated here.)

Formalization notes:
* 2x + y - z is computed in ℤ; powers of eight are 8^j with j ≥ 0.
* Controls (computed): for c = 1, 2, 4 every n < 1500 is represented.
-/

namespace OMA.S_oeis_a284343

/-- Part (i) of the conjecture. -/
theorem main :
    ∀ c : ℕ, c = 1 ∨ c = 2 ∨ c = 4 → ∀ n : ℕ, ∃ x y z w : ℕ, y ≤ z ∧
      x ^ 2 + y ^ 2 + z ^ 2 + w ^ 2 = n ∧
      ((c : ℤ) * (2 * x + y - z) = 0 ∨ ∃ j : ℕ, (c : ℤ) * (2 * x + y - z) = 8 ^ j) := by
  sorry

end OMA.S_oeis_a284343

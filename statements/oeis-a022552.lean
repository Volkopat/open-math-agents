import Mathlib

/-!
# OEIS A022552: `x² + y² + z³` up to `+2`

Source: https://oeis.org/A022552
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

A022552 lists the numbers that are not the sum of two squares and a nonnegative cube. Conjecture
(Sun, quoted in the entry): any `n` can be written as `x² + y² + z³` or `x² + y² + z³ + 2`.

Conventions:
* `n, x, y, z` are natural numbers.
-/

namespace OMA.S_oeis_a022552

/-- Every `n` is `x² + y² + z³` or `x² + y² + z³ + 2`. -/
theorem main : ∀ n : ℕ, ∃ x y z : ℕ,
    n = x ^ 2 + y ^ 2 + z ^ 3 ∨ n = x ^ 2 + y ^ 2 + z ^ 3 + 2 := by
  sorry

end OMA.S_oeis_a022552

import Mathlib

/-!
# Is the identity 2^5 - 5^2 = 2 + 5 unique?

Source: https://math.stackexchange.com/questions/3290080
Credit: @zarnab222-dev

For distinct positive integers, adding b^a to both sides gives an equivalent
equation in the naturals and avoids truncated subtraction.
-/

namespace OMA.S_mse_3290080

theorem main : ∀ a b : ℕ, 0 < a → 0 < b → a ≠ b →
    (a ^ b = b ^ a + a + b ↔ a = 2 ∧ b = 5) := by
  sorry

end OMA.S_mse_3290080

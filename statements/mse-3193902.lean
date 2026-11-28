import Mathlib

/-!
# For every `b`, is there `a` with digit sum of `a^b` equal to `a`?

Source: https://math.stackexchange.com/questions/3193902
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

Conjecture (asker): given a positive integer `b`, there exists a positive integer `a` such that the
decimal digit sum of `a^b` equals `a` (e.g. `9² = 81`, `8³ = 512`, `46⁵ = 205962976`).
-/

namespace OMA.S_mse_3193902

/-- For every `b ≥ 1` some `a ≥ 1` equals the digit sum of `a^b`. -/
theorem main : ∀ b : ℕ, 1 ≤ b → ∃ a : ℕ, 1 ≤ a ∧ (Nat.digits 10 (a ^ b)).sum = a := by
  sorry

end OMA.S_mse_3193902

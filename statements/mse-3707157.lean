import Mathlib

/-!
# Positive integer solutions of `a/(b+c) + b/(a+c) + c/(a+b) = 4`

Source: https://math.stackexchange.com/questions/3707157
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

The asker recalls the (false) conjecture that `a/(b+c) + b/(a+c) + c/(a+b) = 4` has no positive
integer solutions, and asks for a proof that a solution exists without exhibiting one. `main`
states the existence of a positive integer solution.
-/

namespace OMA.S_mse_3707157

/-- The equation has a solution in positive integers. -/
theorem main : ∃ a b c : ℕ, 0 < a ∧ 0 < b ∧ 0 < c ∧
    (a : ℚ) / (b + c) + b / (a + c) + c / (a + b) = 4 := by
  sorry

end OMA.S_mse_3707157

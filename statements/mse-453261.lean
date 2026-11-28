import Mathlib

/-!
# `tan(n) > n` for infinitely many positive integers

Source: https://math.stackexchange.com/questions/453261
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

Open problem quoted by the asker: `tan(n) > n` for infinitely many positive integers `n`
(radians).

Conventions:
* `Real.tan` (at no positive integer is `cos n = 0`, since `π` is irrational).
-/

namespace OMA.S_mse_453261

/-- Infinitely many positive integers `n` satisfy `tan n > n`. -/
theorem main : {n : ℕ | 0 < n ∧ (n : ℝ) < Real.tan n}.Infinite := by
  sorry

end OMA.S_mse_453261

import Mathlib

/-!
# Is `x_{n+1} = x_n - 1/x_n`, `x_0 = 2`, unbounded?

Source: https://math.stackexchange.com/questions/2689843
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

Question: is the sequence `x_{n+1} = x_n - 1/x_n`, `x_0 = 2`, unbounded?

Conventions:
* Real numbers. Lean's `1/0 = 0` makes the definition total; it agrees with the source's
  sequence as long as no iterate is `0`.
* The source asks a yes/no question; `main` states the answer yes (unbounded), and a disproof
  would answer no.
-/

namespace OMA.S_mse_2689843

/-- The sequence. -/
noncomputable def x : ℕ → ℝ
  | 0 => 2
  | n + 1 => x n - 1 / x n

/-- The sequence is unbounded. -/
theorem main : ∀ B : ℝ, ∃ n : ℕ, B < |x n| := by
  sorry

end OMA.S_mse_2689843

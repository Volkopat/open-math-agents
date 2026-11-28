import Mathlib

/-!
# Twin prime indices between consecutive twin-prime squares

Source: https://math.stackexchange.com/questions/5135958
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

Let `T = {k ∈ ℕ | 6k - 1 and 6k + 1 are prime}`. Conjecture (asker): for every `k ∈ T` there is
`n ∈ T` with `(6k - 1)² < 6n - 1 < 6n + 1 < (6k + 1)²`, i.e. `6k² - 2k < n < 6k² + 2k`.

Conventions:
* `k ≥ 1`.
-/

namespace OMA.S_mse_5135958

/-- `k` is a twin prime index. -/
def InT (k : ℕ) : Prop := 1 ≤ k ∧ (6 * k - 1).Prime ∧ (6 * k + 1).Prime

/-- Every twin prime index `k` has another one in `(6k² - 2k, 6k² + 2k)`. -/
theorem main : ∀ k : ℕ, InT k → ∃ n : ℕ, InT n ∧ 6 * k ^ 2 - 2 * k < n ∧ n < 6 * k ^ 2 + 2 * k := by
  sorry

end OMA.S_mse_5135958

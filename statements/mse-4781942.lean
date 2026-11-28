import Mathlib

/-!
# Proportion of positive terms of `a_n = sec(a_{n-1})`

Source: https://math.stackexchange.com/questions/4781942
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

Conjecture (asker): if `a₁ ∈ ℤ` and `aₙ = sec(a_{n-1})` for `n > 1`, then the proportion of
positive terms among `a₁, …, a_N` tends to `1/√(2π)` as `N → ∞`.

Conventions:
* `sec x = 1/cos x` (Lean's `1/0 = 0` makes the sequence total; it agrees with the source as long
  as no `cos aₙ` vanishes). Indexing from `0`: `a 0 = a₁`.
-/

namespace OMA.S_mse_4781942

open Filter Topology

/-- The sequence with integer start `a₁`. -/
noncomputable def a (a₁ : ℤ) : ℕ → ℝ
  | 0 => a₁
  | n + 1 => 1 / Real.cos (a a₁ n)

/-- The proportion of positive terms tends to `1/√(2π)`. -/
theorem main : ∀ a₁ : ℤ, Tendsto (fun N : ℕ =>
    (((Finset.range N).filter fun n => 0 < a a₁ n).card : ℝ) / N) atTop
    (𝓝 (1 / Real.sqrt (2 * Real.pi))) := by
  sorry

end OMA.S_mse_4781942

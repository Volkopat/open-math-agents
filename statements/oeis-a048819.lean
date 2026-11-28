import Mathlib

/-!
# OEIS A048819: fixed points of Minkowski's question mark function

Source: https://oeis.org/A048819
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

Conjecture (Gayfulin–Shulga, Conjecture 1, quoted in the entry): Minkowski's question mark
function `?` has exactly five fixed points on `[0, 1]`.

Conventions:
* `?` on `[0, 1]` is the unique continuous `f : [0,1] → ℝ` with `f(x/(1+x)) = f(x)/2` and
  `f(1 - x) = 1 - f(x)` for `x ∈ [0, 1]` (de Rham's characterisation). `main` quantifies over every
  continuous `f` with these two equations (so it does not rely on uniqueness) and states that
  `{x ∈ [0, 1] | f x = x}` has exactly five elements.
-/

namespace OMA.S_oeis_a048819

open Set

/-- Minkowski's `?` has exactly five fixed points in `[0, 1]`. -/
theorem main : ∀ f : ℝ → ℝ, ContinuousOn f (Icc 0 1) →
    (∀ x ∈ Icc (0 : ℝ) 1, f (x / (1 + x)) = f x / 2) →
    (∀ x ∈ Icc (0 : ℝ) 1, f (1 - x) = 1 - f x) →
    {x ∈ Icc (0 : ℝ) 1 | f x = x}.ncard = 5 := by
  sorry

end OMA.S_oeis_a048819

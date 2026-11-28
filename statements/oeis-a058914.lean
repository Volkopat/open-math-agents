import Mathlib

/-!
# OEIS A058914: fixed points of Minkowski's question-mark function

Source: https://oeis.org/A058914
It is conjectured that Minkowski's question-mark function `?` has exactly five fixed points on
`[0, 1]` (four modulo `1`): `0`, `1/2`, `1` and two irrational points (Gayfulin–Shulga,
Conjecture 1).

Conventions. `?` is characterised on `[0, 1]` as the unique continuous function with
`?(x/(x+1)) = ?(x)/2` and `?(1 - x) = 1 - ?(x)` for `x ∈ [0, 1]` (these functional equations
together with continuity determine `?`); `main` quantifies over every such function.

-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
-/

namespace OMA.S_oeis_a058914

open Set

theorem main :
    ∀ f : ℝ → ℝ, ContinuousOn f (Icc 0 1) →
      (∀ x ∈ Icc (0 : ℝ) 1, f (x / (x + 1)) = f x / 2) →
      (∀ x ∈ Icc (0 : ℝ) 1, f (1 - x) = 1 - f x) →
      {x ∈ Icc (0 : ℝ) 1 | f x = x}.ncard = 5 := by
  sorry

end OMA.S_oeis_a058914

import Mathlib

/-!
# A026368: Positions of 0 in the fixed point of the morphism 0 -> 11, 1 -> 110

Source: https://oeis.org/A026368
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
-- Draft from an earlier generic agent run; audited against the source and checked by this agent.

Conjecture:
Let a(n) (for n >= 1) be the n-th 1-based position of 0 in the fixed point of the morphism
0 -> 11, 1 -> 110 (starting from 1). Then for all n >= 1,
  -2 < n * r - a(n) < 4,
where r = 2 + sqrt(3).
-/

namespace OMA.S_oeis_a026368

/-- The morphism 0 -> 11, 1 -> 110 represented on Bool (false = 0, true = 1). -/
def morphStep (w : List Bool) : List Bool :=
  w.flatMap (fun b => if b then [true, true, false] else [true, true])

/-- The k-th symbol (0-indexed) of the fixed point of morphStep starting from [true]. -/
def fixedPoint (k : ℕ) : Bool :=
  (morphStep^[k + 1] [true]).getD k true

/-- The n-th 1-based position of 0 (false) in the fixed point (for n >= 1). -/
noncomputable def a (n : ℕ) : ℕ :=
  Nat.nth (fun k => fixedPoint k = false) (n - 1) + 1

/-- Conjecture: -2 < n * (2 + sqrt 3) - a(n) < 4 for all n >= 1. -/
theorem main :
    ∀ n : ℕ, 1 ≤ n →
      (-2 : ℝ) < (n : ℝ) * (2 + Real.sqrt 3) - (a n : ℝ) ∧
      (n : ℝ) * (2 + Real.sqrt 3) - (a n : ℝ) < 4 := by
  sorry

end OMA.S_oeis_a026368

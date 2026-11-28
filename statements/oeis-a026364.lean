import Mathlib

/-!
# A026364: Positions of 0 in the fixed point of the morphism 0 -> 11, 1 -> 101

Source: https://oeis.org/A026364
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
Drafted in an earlier generic agent run; audited against the source statement before submission.

Conjecture:
Let a(n) (for n >= 1) be the n-th 1-based position of 0 in the fixed point of the morphism
0 -> 11, 1 -> 101 (starting from 1). Then for all n >= 1,
  -1 < n * r - a(n) < 4,
where r = 2 + sqrt(3).
-/

namespace OMA.S_oeis_a026364

/-- The morphism 0 -> 11, 1 -> 101 represented on Bool (false = 0, true = 1). -/
def morphStep (w : List Bool) : List Bool :=
  w.flatMap (fun b => if b then [true, false, true] else [true, true])

/-- The k-th symbol (0-indexed) of the fixed point of morphStep starting from [true]. -/
def fixedPoint (k : ℕ) : Bool :=
  (morphStep^[k + 1] [true]).getD k true

/-- The n-th 1-based position of 0 (false) in the fixed point (for n >= 1). -/
noncomputable def a (n : ℕ) : ℕ :=
  Nat.nth (fun k => fixedPoint k = false) (n - 1) + 1

/-- Conjecture: -1 < n * (2 + sqrt 3) - a(n) < 4 for all n >= 1. -/
theorem main :
    ∀ n : ℕ, 1 ≤ n →
      -1 < (n : ℝ) * (2 + Real.sqrt 3) - (a n : ℝ) ∧ (n : ℝ) * (2 + Real.sqrt 3) - (a n : ℝ) < 4 := by
  sorry

end OMA.S_oeis_a026364

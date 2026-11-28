import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# A first-order difference estimate for real powers

Source: https://mathoverflow.net/questions/130917/analysis-question-related-to-lp-type-inequalities
Question by Craig, 17 May 2013, CC BY-SA 3.0.
Credit: @etaubman

The quantifiers and all four terms of the proposed bound are preserved.
Real exponentiation is applied only to nonnegative absolute values.
-/

namespace OMA.S_mo_130917

theorem main : ∀ p : ℝ, 1 < p → ∃ C : ℝ, ∀ x y : ℝ,
    |(|x + 1| ^ p - |y + 1| ^ p) - p * (x - y)| ≤
      C * (|x| + |y| + |x| ^ (p - 1) + |y| ^ (p - 1)) * |x - y| := by
  sorry

end OMA.S_mo_130917

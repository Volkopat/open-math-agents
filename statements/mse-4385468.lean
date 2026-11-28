import Mathlib

/-!
# Convergence of 1 / (n^p sin(n)) to Zero

Source: https://math.stackexchange.com/questions/4385468/does-there-exist-any-p-0-such-that-frac1np-sinn-to-0-n-to-inft
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
-- Draft from an earlier generic agent run; audited against the source and checked by this agent.

## Problem Statement
Does there exist a real number `p > 0` such that
`1 / (n^p * sin(n)) → 0` as `n → +∞`?

## Formalization Notes
This is directly linked to the irrationality measure `μ(π)` of `π`: such `p`
exists iff `π` has finite irrationality measure (which is known, e.g., `μ(π) ≤ 7.1032...`
by Zeilberger–Zudilin), with the infimum of such `p` equal to `μ(π) - 1`.
-/

namespace OMA.S_mse_4385468

theorem main :
    ∃ p : ℝ, 0 < p ∧
      Filter.Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) ^ p * Real.sin n))
        Filter.atTop (nhds 0) := by
  sorry

end OMA.S_mse_4385468

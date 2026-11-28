import Mathlib

/-!
# A099500: Number of distinct products of subsets of integers in the interval [n^2+1, (n+1)^2-1] which are twice a square.

Source: https://oeis.org/A099500
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
Drafted in an earlier generic agent run; audited against the source statement before submission.

Kaplansky's conjecture (proved by Granville and Selfridge): for every `n ≥ 1`, there exists
a subset of integers in `[n^2 + 1, (n + 1)^2 - 1]` whose product is twice a square.
-/

namespace OMA.S_oeis_a099500

theorem main :
    ∀ n : ℕ, 1 ≤ n →
      ∃ S : Finset ℕ, S ⊆ Finset.Icc (n ^ 2 + 1) ((n + 1) ^ 2 - 1) ∧
        ∃ m : ℕ, ∏ x ∈ S, x = 2 * m ^ 2 := by
  sorry

end OMA.S_oeis_a099500

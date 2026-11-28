import Mathlib

/-!
# A007972: Number of permutations that are 2 "block reversals" away from 12...n

Source: https://oeis.org/A007972
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
-- Draft from an earlier generic agent run; audited against the source and checked by this agent.

Conjecture (proved up to offset by C. Homberger):
For every m >= 3, the number of permutations of {0, 1, ..., m - 1} at block-reversal distance
exactly 2 from the identity permutation [0, 1, ..., m - 1] is
  ((m - 2)^4 + 6*(m - 2)^3 + 11*(m - 2)^2 - 12*(m - 2) + 6) / 6.

Conventions:
A block reversal reverses a contiguous sublist of length at least 2.
With n = m - 2 (for m >= 3), the formula becomes (n^4 + 6*n^3 + 11*n^2 - 12*n + 6) / 6:
  m = 3 (n = 1): 2
  m = 4 (n = 2): 15
  m = 5 (n = 3): 52.
-/

namespace OMA.S_oeis_a007972

/-- One block reversal step: reverse a contiguous subsegment of length >= 2. -/
def RevStep (u v : List ℕ) : Prop :=
  ∃ a b c : List ℕ, 2 ≤ b.length ∧ u = a ++ b ++ c ∧ v = a ++ b.reverse ++ c

/-- The set of permutations of [0, ..., m - 1] at exact block-reversal distance 2 from identity. -/
def distTwoPerms (m : ℕ) : Set (List ℕ) :=
  {w : List ℕ | w ≠ List.range m ∧ ¬ RevStep (List.range m) w ∧
    ∃ u : List ℕ, RevStep (List.range m) u ∧ RevStep u w}

/-- Conjectured closed form for the number of permutations at reversal distance 2. -/
theorem main :
    ∀ n : ℕ, 1 ≤ n →
      (distTwoPerms (n + 2)).ncard =
        (n ^ 4 + 6 * n ^ 3 + 11 * n ^ 2 - 12 * n + 6) / 6 := by
  sorry

end OMA.S_oeis_a007972

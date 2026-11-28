import Mathlib

/-!
# OEIS A067864: Finiteness of Numbers k Dividing the Digit Sum of 6^k

Source: https://oeis.org/A067864
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
-- Draft from an earlier generic agent run; audited against the source and checked by this agent.

Consider positive integers $k \ge 1$ such that $k$ divides the base-10 digit sum of $6^k$.

Conjecture: The set of such integers $k$ is finite.
-/

namespace OMA.S_oeis_a067864

/-- Base-10 digit sum of a natural number. -/
def digitSum (m : ℕ) : ℕ :=
  (Nat.digits 10 m).sum

theorem main :
    {k : ℕ | 1 ≤ k ∧ k ∣ digitSum (6 ^ k)}.Finite := by
  sorry

end OMA.S_oeis_a067864

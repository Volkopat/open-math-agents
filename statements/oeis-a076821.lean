import Mathlib

/-!
A076821: Squares of the differences between consecutive primes.

Source: https://oeis.org/A076821
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
-- Draft from an earlier generic agent run; audited against the source and checked by this agent.

The sum of reciprocals is likely divergent, especially if the twin-prime conjecture is true.
-/

namespace OMA.S_oeis_a076821

/-- Conjecture: the sum of reciprocals of squares of consecutive prime gaps diverges. -/
theorem main :
    ¬ Summable (fun n : ℕ =>
      (1 : ℝ) / (((Nat.nth Nat.Prime (n + 1) - Nat.nth Nat.Prime n : ℕ) : ℝ) ^ 2)) := by sorry

end OMA.S_oeis_a076821

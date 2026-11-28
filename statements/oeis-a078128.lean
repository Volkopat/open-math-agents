import Mathlib

/-!
# A078128: Number of ways to write n as sum of cubes > 1.

Source: https://oeis.org/A078128
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
-- Draft from an earlier generic agent run; audited against the source and checked by this agent.

Conjecture (lower bound): for all k there exists b(k) such that a(n) > k for n > b(k);
see b(0) = A078129(83) = 154 and b(1) = A078130(63) = 218.
-/

namespace OMA.S_oeis_a078128

/-- Number of partitions of `n` into cubes greater than `1`. -/
noncomputable def a (n : ℕ) : ℕ :=
  Nat.card { P : Nat.Partition n // ∀ p ∈ P.parts, ∃ m : ℕ, 2 ≤ m ∧ p = m ^ 3 }

theorem main :
    ∀ k : ℕ, ∃ b : ℕ, ∀ n : ℕ, b < n → k < a n := by sorry

end OMA.S_oeis_a078128

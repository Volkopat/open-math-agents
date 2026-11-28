import Mathlib

/-!
# A046921: Goldbach's conjecture on representations of odd numbers as p + 2a^2

Source: https://oeis.org/A046921
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
-- Draft from an earlier generic agent run; audited against the source and checked by this agent.

Title: A046921: Number of ways to express 2n+1 as p+2a^2; p = 1 or prime, a >= 0.

Statement:
Goldbach conjectured this sequence is never zero.
-/

namespace OMA.S_oeis_a046921

theorem main :
    ∀ n : ℕ, ∃ p a : ℕ, (p = 1 ∨ Nat.Prime p) ∧ 2 * n + 1 = p + 2 * a ^ 2 := by
  sorry

end OMA.S_oeis_a046921

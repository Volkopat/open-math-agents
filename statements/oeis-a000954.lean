import Mathlib

/-!
# A000954: Goldbach's Conjecture

Source: https://oeis.org/A000954
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
Drafted in an earlier generic agent run; audited against the source statement before submission.

A000954 concerns the number of ways an even integer can be written as an unordered sum of two
primes.

Conjecture (Goldbach): Every even integer greater than `2` is the sum of two primes.
-/

namespace OMA.S_oeis_a000954

theorem main :
    ∀ n : ℕ, 2 < n → Even n → ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ p + q = n := by
  sorry

end OMA.S_oeis_a000954

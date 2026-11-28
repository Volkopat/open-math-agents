import Mathlib

/-!
# OEIS A059998: Primes occurring in ternary Goldbach representations

Source: https://oeis.org/A059998
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
Drafted in an earlier generic agent run; audited against the source statement before submission.

Conjecture (Ternary Goldbach conjecture): Every integer greater than 5 can be
written as the sum of three primes.
-/

namespace OMA.S_oeis_a059998

theorem main :
    ∀ n : ℕ, 5 < n →
      ∃ p q r : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ Nat.Prime r ∧ p + q + r = n := by
  sorry

end OMA.S_oeis_a059998

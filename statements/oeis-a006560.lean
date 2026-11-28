import Mathlib

/-!
# A006560: Arbitrarily Long Arithmetic Progressions of Consecutive Primes

Source: https://oeis.org/A006560
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
Drafted in an earlier generic agent run; audited against the source statement before submission.

A006560(n) is the smallest starting prime for an arithmetic progression of `n` consecutive primes.

Conjecture: For every positive integer `n`, there exist `n` consecutive primes in arithmetic
progression.
-/

namespace OMA.S_oeis_a006560

theorem main :
    ∀ n : ℕ, 1 ≤ n →
      ∃ i d : ℕ, 0 < d ∧ ∀ k < n, Nat.nth Nat.Prime (i + k) = Nat.nth Nat.Prime i + k * d := by
  sorry

end OMA.S_oeis_a006560

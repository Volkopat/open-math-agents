import Mathlib

/-!
# A005097: (Odd primes - 1)/2

Source: https://oeis.org/A005097
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
Drafted in an earlier generic agent run; audited against the source statement before submission.

## Problem Statement
Let A005097 be the sequence of numbers `(p - 1) / 2` where `p` ranges over the odd primes
(i.e. positive integers `a` such that `2 * a + 1` is prime).

Conjecture: The set of pairwise sums of terms of A005097 is the set of all integers greater
than 1, i.e., every integer `n ≥ 2` can be written as `a + b` where `2 * a + 1` and `2 * b + 1`
are odd primes. (This is equivalent to Goldbach's conjecture that every even integer `≥ 6` is
the sum of two odd primes.)
-/

namespace OMA.S_oeis_a005097

/-- Membership in A005097: `a ≥ 1` such that `2 * a + 1` is an odd prime. -/
def inA005097 (a : ℕ) : Prop :=
  1 ≤ a ∧ Nat.Prime (2 * a + 1)

theorem main :
    ∀ n : ℕ, 2 ≤ n → ∃ a b : ℕ, inA005097 a ∧ inA005097 b ∧ a + b = n := by
  sorry

end OMA.S_oeis_a005097

import Mathlib

/-!
# A082512: a(n) = p is the smallest prime introducing a consecutive prime-difference pattern as follows: [2,2n,2]

Source: https://oeis.org/A082512
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
Drafted in an earlier generic agent run; audited against the source statement before submission.

It is conjectured that the twin primes in the neighborhood can be separated by an arbitrarily large gap.
-/

namespace OMA.S_oeis_a082512

noncomputable def nthPrime (k : ℕ) : ℕ :=
  Nat.nth Nat.Prime k

theorem main :
    ∀ N : ℕ, ∃ k : ℕ,
      nthPrime (k + 1) - nthPrime k = 2 ∧
      nthPrime (k + 3) - nthPrime (k + 2) = 2 ∧
      N ≤ nthPrime (k + 2) - nthPrime (k + 1) := by
  sorry

end OMA.S_oeis_a082512

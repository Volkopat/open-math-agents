import Mathlib

/-!
# OEIS A101462: smallest k with 2^k - prime(n) prime

Source: https://oeis.org/A101462
`a n` is the smallest `k` such that `2^k - prime(n)` is prime. Conjecture: the sequence is
defined for all `n`, i.e. for every prime `p` there is `k` with `2^k - p` prime.

-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
-/

namespace OMA.S_oeis_a101462

theorem main : ∀ p : ℕ, p.Prime → ∃ k : ℕ, p < 2 ^ k ∧ (2 ^ k - p).Prime := by
  sorry

end OMA.S_oeis_a101462

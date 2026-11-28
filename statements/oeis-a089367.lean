import Mathlib

/-!
# OEIS A089367: smallest prime p with np + 1 prime

Source: https://oeis.org/A089367
`a n` is the smallest prime `p` such that `n p + 1` is prime, or `0` if none exists.
`a(2m+1) = 0` when `4m+3` is composite (for odd `n` only `p = 2` can work). Conjecture: there
are no other zeros, i.e. for every even `n ≥ 2` there is a prime `p` with `n p + 1` prime
(the odd case is settled by the remark).

-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
-/

namespace OMA.S_oeis_a089367

theorem main : ∀ n : ℕ, 2 ≤ n → Even n → ∃ p : ℕ, p.Prime ∧ (n * p + 1).Prime := by
  sorry

end OMA.S_oeis_a089367

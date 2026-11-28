import Mathlib

/-!
# OEIS A090530: twin primes around multiples of each prime

Source: https://oeis.org/A090530
`a n` is the least multiple `k` of `prime(n)` such that `(k-1, k+1)` is a twin prime pair, or `0`
if none exists. Conjecture: no term is zero, i.e. every prime `p` has a multiple `k` with
`k - 1` and `k + 1` both prime.

-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
-/

namespace OMA.S_oeis_a090530

theorem main :
    ∀ p : ℕ, p.Prime → ∃ k : ℕ, 0 < k ∧ p ∣ k ∧ (k - 1).Prime ∧ (k + 1).Prime := by
  sorry

end OMA.S_oeis_a090530

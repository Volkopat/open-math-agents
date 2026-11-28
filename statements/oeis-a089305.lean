import Mathlib

/-!
# OEIS A089305: primes of the form n(n+1)⋯(n+k) + 1

Source: https://oeis.org/A089305
`a n` is the smallest prime of the form `n (n+1) ⋯ (n+k) + 1` with `k > 0`, or `0` if no such
prime exists. Conjecture: no entry is zero.

Conventions. `n ≥ 1`.

-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
-/

namespace OMA.S_oeis_a089305

theorem main :
    ∀ n : ℕ, 1 ≤ n → ∃ k : ℕ, 0 < k ∧ ((∏ i ∈ Finset.range (k + 1), (n + i)) + 1).Prime := by
  sorry

end OMA.S_oeis_a089305

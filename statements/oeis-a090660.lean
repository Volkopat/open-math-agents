import Mathlib

/-!
# OEIS A090660: consecutive factorial primes n! + 1

Source: https://oeis.org/A090660
Comment on the entry: one can conjecture that for `n > 2`, if `n! + 1` is prime then
`(n+1)! + 1` is not prime.

-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
-/

namespace OMA.S_oeis_a090660

theorem main : ∀ n : ℕ, 2 < n → (n.factorial + 1).Prime → ¬ ((n + 1).factorial + 1).Prime := by
  sorry

end OMA.S_oeis_a090660

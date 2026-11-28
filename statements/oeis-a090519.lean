import Mathlib

/-!
# OEIS A090519: primes p with ⌊10^n / p⌋ prime

Source: https://oeis.org/A090519
`a n` is the smallest prime `p` such that `⌊10^n / p⌋` is prime, or `0` if no such number exists.
Conjecture: no term is zero.

Conventions. `n ≥ 1`.

-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
-/

namespace OMA.S_oeis_a090519

theorem main : ∀ n : ℕ, 1 ≤ n → ∃ p : ℕ, p.Prime ∧ (10 ^ n / p).Prime := by
  sorry

end OMA.S_oeis_a090519

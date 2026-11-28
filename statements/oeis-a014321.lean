import Mathlib

/-!
# A014321: The next new gap between successive odd primes (divided by 2)

Source: https://oeis.org/A014321
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
-- Draft from an earlier generic agent run; audited against the source and checked by this agent.

Conjecture (weak Polignac's conjecture):
Every positive even integer occurs at least once as the difference between two consecutive primes,
so that A014321 is a permutation of the positive integers.

Conventions:
- `Nat.nth Nat.Prime n` denotes the `n`-th prime (0-indexed: `p(0) = 2, p(1) = 3, ...`).
- For every `d ≥ 1`, there exists `n` such that `p(n + 1) - p(n) = 2 * d`.
-/

namespace OMA.S_oeis_a014321

theorem main :
    ∀ d : ℕ, d ≥ 1 →
      ∃ n : ℕ, Nat.nth Nat.Prime (n + 1) - Nat.nth Nat.Prime n = 2 * d := by
  sorry

end OMA.S_oeis_a014321

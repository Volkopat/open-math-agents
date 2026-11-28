import Mathlib

/-!
# A014664: Order of 2 modulo prime powers for non-Wieferich primes

Source: https://oeis.org/A014664
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
-- Draft from an earlier generic agent run; audited against the source and checked by this agent.

## Problem Statement
Let `a(n)` be the multiplicative order of `2` modulo the `n`-th odd prime `p`.
Note that `A002326(m)` is the multiplicative order of `2` modulo `2*m + 1`, so
`A002326((p^k - 1) / 2)` is the multiplicative order of `2` modulo `p^k`.

Conjecture: If `p` is an odd prime that is not a Wieferich prime (i.e., `p^2 ∤ 2^(p - 1) - 1`),
then for every `k ≥ 1`, the multiplicative order of `2` modulo `p^k` equals
`ord_p(2) * p^(k - 1)`.
-/

namespace OMA.S_oeis_a014664

theorem main :
    ∀ p k : ℕ, Nat.Prime p → Odd p → ¬ (p ^ 2 ∣ 2 ^ (p - 1) - 1) → 1 ≤ k →
      orderOf (2 : ZMod (p ^ k)) = orderOf (2 : ZMod p) * p ^ (k - 1) := by
  sorry

end OMA.S_oeis_a014664

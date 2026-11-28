import Mathlib

/-!
# A095017: Number of lesser twin primes (A001359) in range ]2^n, 2^(n+1)].

Source: https://oeis.org/A095017
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
-- Draft from an earlier generic agent run; audited against the source and checked by this agent.

Conjecture: a(n) > 0 for all n (n >= 1). This holds for all n <= 100.
-/

namespace OMA.S_oeis_a095017

theorem main :
    ∀ n : ℕ, 1 ≤ n →
      ∃ p : ℕ, 2 ^ n < p ∧ p ≤ 2 ^ (n + 1) ∧ p.Prime ∧ (p + 2).Prime := by
  sorry

end OMA.S_oeis_a095017

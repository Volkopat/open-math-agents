import Mathlib

/-!
# A087243: Primes arising as n + A087242(n)

Source: https://oeis.org/A087243
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
-- Draft from an earlier generic agent run; audited against the source and checked by this agent.

If n is odd, a(n) is either n+2 (if n+2 is prime) or 0; if n is even, a(n) is
the least prime p such that p - n is prime. Polignac's conjecture implies that
such a prime exists for every positive even n.
-/

namespace OMA.S_oeis_a087243

theorem main :
    ∀ n : ℕ, 0 < n → Even n → ∃ p : ℕ, p.Prime ∧ n < p ∧ (p - n).Prime := by
  sorry

end OMA.S_oeis_a087243

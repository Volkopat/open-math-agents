import Mathlib

/-!
# A031172: a(n) = prime(n+10) - prime(n)

Source: https://oeis.org/A031172
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
-- Draft from an earlier generic agent run; audited against the source and checked by this agent.

Conjecture (prime k-tuple conjecture for k = 11):
The minimal admissible diameter of an 11-tuple of consecutive primes is 36, and it occurs
infinitely often: there are infinitely many n such that prime(n + 10) - prime(n) = 36.
-/

namespace OMA.S_oeis_a031172

/-- Conjecture: prime(n + 10) - prime(n) = 36 for infinitely many n. -/
theorem main :
    {n : ℕ | Nat.nth Nat.Prime (n + 10) - Nat.nth Nat.Prime n = 36}.Infinite := by
  sorry

end OMA.S_oeis_a031172

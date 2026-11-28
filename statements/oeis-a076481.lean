import Mathlib

/-!
A076481: Primes of the form (3^n-1)/2.

Source: https://oeis.org/A076481
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
-- Draft from an earlier generic agent run; audited against the source and checked by this agent.

Conjecture: primes p such that sigma(2p+1) = 3*p+1. Sigma(2*a(n)+1) = 3*a(n) +1 holds for all first 9 terms.
-/

namespace OMA.S_oeis_a076481

/-- Conjecture: a prime `p` is of the form `(3^n - 1) / 2` if and only if `sigma(2p + 1) = 3p + 1`. -/
theorem main :
    ∀ p : ℕ, Nat.Prime p →
      ((∃ n : ℕ, 2 * p + 1 = 3 ^ n) ↔ ArithmeticFunction.sigma 1 (2 * p + 1) = 3 * p + 1) := by sorry

end OMA.S_oeis_a076481

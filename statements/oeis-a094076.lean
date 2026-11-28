import Mathlib

/-!
# A094076: Smallest k such that prime(n) + 2^k is prime, or -1 if no such prime exists.

Source: https://oeis.org/A094076
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
Drafted in an earlier generic agent run; audited against the source statement before submission.

Conjecture: k > 0 for all n (i.e., for every prime p there exists k >= 0 such that
p + 2^k is prime; for odd primes p, k > 0).
-/

namespace OMA.S_oeis_a094076

theorem main :
    ∀ p : ℕ, p.Prime → ∃ k : ℕ, (p + 2 ^ k).Prime := by
  sorry

end OMA.S_oeis_a094076

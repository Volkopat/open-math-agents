import Mathlib

/-!
# A100873: Pseudotwinprimes p+2 for primes p such that p+2 divides p^(p+2)+2 and p+2 is composite.

Source: https://oeis.org/A100873
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
Drafted in an earlier generic agent run; audited against the source statement before submission.

Conjecture 1: If `p` and `p + 2` are prime (twin primes), then `p + 2` divides `p^(p + 2) + 2`.
-/

namespace OMA.S_oeis_a100873

theorem main :
    ∀ p : ℕ, Nat.Prime p → Nat.Prime (p + 2) → (p + 2) ∣ p ^ (p + 2) + 2 := by
  sorry

end OMA.S_oeis_a100873

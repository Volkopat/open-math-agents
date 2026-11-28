import Mathlib

/-!
# A092067: a(n) is the smallest number m such that m > 1 and m divides n^m + 1.

Source: https://oeis.org/A092067
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
-- Draft from an earlier generic agent run; audited against the source and checked by this agent.

Conjecture 1: All terms of this sequence are primes. We know if n is odd a(n) is the
smallest prime factor of n+1.
-/

namespace OMA.S_oeis_a092067

noncomputable def a (n : ℕ) : ℕ :=
  sInf {m : ℕ | 1 < m ∧ m ∣ n ^ m + 1}

theorem main :
    ∀ n : ℕ, 1 ≤ n → Nat.Prime (a n) := by
  sorry

end OMA.S_oeis_a092067

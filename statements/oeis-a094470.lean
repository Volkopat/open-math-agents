import Mathlib

/-!
# A094470: Numbers k such that phi(k) | sigma_18(k).

Source: https://oeis.org/A094470
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
-- Draft from an earlier generic agent run; audited against the source and checked by this agent.

sigma_18(n) is the sum of the 18th powers of the divisors of n (A013966).
Conjecture: analogous sequences with any 4j+2 exponent instead of 18,
includes all terms of A015759 [with exponent=2].
-/

namespace OMA.S_oeis_a094470

/-- Sum of the `m`-th powers of the divisors of `k`. -/
def sigmaPow (m k : ℕ) : ℕ :=
  ∑ d ∈ k.divisors, d ^ m

theorem main :
    ∀ j k : ℕ, 1 ≤ k → Nat.totient k ∣ sigmaPow 2 k →
      Nat.totient k ∣ sigmaPow (4 * j + 2) k := by
  sorry

end OMA.S_oeis_a094470

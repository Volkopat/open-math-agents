import Mathlib

/-!
# A087564: Smallest prime of the form n*(n+1)*...*(n+k) + 1

Source: https://oeis.org/A087564
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
-- Draft from an earlier generic agent run; audited against the source and checked by this agent.

a(n) = smallest prime of the form n*(n+1)*(n+2)*...*(n+k) + 1 (for k >= 0), or
0 if no such prime exists. Conjecture: No term is zero (for all n >= 1).
-/

namespace OMA.S_oeis_a087564

theorem main :
    ∀ n : ℕ, 1 ≤ n →
      ∃ k : ℕ, ((∏ i ∈ Finset.range (k + 1), (n + i)) + 1).Prime := by
  sorry

end OMA.S_oeis_a087564

import Mathlib

/-!
A075555: Smallest prime p such that p+n is a square, or 0 if no such p exists.

Source: https://oeis.org/A075555
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
-- Draft from an earlier generic agent run; audited against the source and checked by this agent.

If n=A047845(i)^2 for some i, i.e. if n has the form ((k-1)/2)^2 with k odd but not prime, then a(n)=0. It is conjectured that these are the only values of n for which a(n)=0; this would follow from Schinzel's hypothesis.
-/

namespace OMA.S_oeis_a075555

/-- Conjecture: there is no prime `p` with `p + n` a square if and only if `n = m^2` for some `m`
such that `2 * m + 1` is not prime. -/
theorem main :
    ∀ n : ℕ, (¬ ∃ p r : ℕ, Nat.Prime p ∧ p + n = r ^ 2) ↔
      ∃ m : ℕ, n = m ^ 2 ∧ ¬ Nat.Prime (2 * m + 1) := by sorry

end OMA.S_oeis_a075555

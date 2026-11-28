import Mathlib

/-!
# A092969: a(1) = 2; for n>1, a(n) = largest prime of the form n!/k + 1, where k < n, or 0 if no such prime exists.

Source: https://oeis.org/A092969
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
Drafted in an earlier generic agent run; audited against the source statement before submission.

Conjecture: There are only finitely many zeros in this sequence.
-/

namespace OMA.S_oeis_a092969

theorem main :
    {n : ℕ | 1 < n ∧ ∀ k : ℕ, 1 ≤ k → k < n → ¬ Nat.Prime (Nat.factorial n / k + 1)}.Finite := by
  sorry

end OMA.S_oeis_a092969

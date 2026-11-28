import Mathlib

/-!
# A092984: a(n) = the least k >= 1 such that n! + k is squarefree.

Source: https://oeis.org/A092984
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
Draft from an earlier generic agent run; audited against the source and re-checked before submission.

Conjecture: There exists a finite k such that a(n) < k for all n.
-/

namespace OMA.S_oeis_a092984

noncomputable def a (n : ℕ) : ℕ :=
  sInf {k : ℕ | 1 ≤ k ∧ Squarefree (Nat.factorial n + k)}

theorem main :
    ∃ K : ℕ, ∀ n : ℕ, a n < K := by
  sorry

end OMA.S_oeis_a092984

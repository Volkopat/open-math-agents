import Mathlib

/-!
# A085929: Smaller of two consecutive numbers with the same prime signature not occurring earlier.

Source: https://oeis.org/A085929
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
Drafted in an earlier generic agent run; audited against the source statement before submission.

Conjecture: (1) The sequence is infinite.
-/

namespace OMA.S_oeis_a085929

noncomputable def primeSignature (n : ℕ) : Multiset ℕ :=
  n.factorization.support.val.map n.factorization

theorem main :
    {s : Multiset ℕ | ∃ k : ℕ, 1 ≤ k ∧ primeSignature k = s ∧ primeSignature (k + 1) = s}.Infinite := by
  sorry

end OMA.S_oeis_a085929

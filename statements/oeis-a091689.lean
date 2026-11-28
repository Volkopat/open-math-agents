import Mathlib

/-!
# A091689: Smallest partition number with n-th prime as factor.

Source: https://oeis.org/A091689
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
Drafted in an earlier generic agent run; audited against the source statement before submission.

Erdős conjectured that every prime divides at least one value of the partition function,
see Ahlgren and Ono link.
-/

namespace OMA.S_oeis_a091689

theorem main :
    ∀ p : ℕ, Nat.Prime p → ∃ n : ℕ, p ∣ Fintype.card (Nat.Partition n) := by
  sorry

end OMA.S_oeis_a091689

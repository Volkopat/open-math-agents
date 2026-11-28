import Mathlib

/-!
# A071387: Carmichael's totient function conjecture

Source: https://oeis.org/A071387
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
Drafted in an earlier generic agent run; audited against the source statement before submission.

Title: A071387: Smallest number k for which the set of solutions to phi(x) = k has 2n-1 entries.

Statement:
a(1) = 0 because of Carmichael's conjecture: there is no positive integer k for which
the equation phi(x) = k has a unique solution x >= 1.
-/

namespace OMA.S_oeis_a071387

theorem main :
    ∀ x : ℕ, 1 ≤ x → ∃ y : ℕ, 1 ≤ y ∧ y ≠ x ∧ Nat.totient y = Nat.totient x := by
  sorry

end OMA.S_oeis_a071387

import Mathlib

/-!
# A087554: Smallest k >= n such that n*k + 1 is prime

Source: https://oeis.org/A087554
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
Drafted in an earlier generic agent run; audited against the source statement before submission.

a(n) = smallest number k >= n such that n*k + 1 is prime.
Conjectures:
(1) a(n) < 2*n for all n >= 1.
(2) For every n >= 2 and every r >= 1, there exists S with n*r < S < n*(r+1)
    such that n*S + 1 is prime.
-/

namespace OMA.S_oeis_a087554

theorem main :
    (∀ n : ℕ, 1 ≤ n → ∃ k : ℕ, n ≤ k ∧ k < 2 * n ∧ (n * k + 1).Prime) ∧
    (∀ n r : ℕ, 2 ≤ n → 1 ≤ r →
      ∃ S : ℕ, n * r < S ∧ S < n * (r + 1) ∧ (n * S + 1).Prime) := by
  sorry

end OMA.S_oeis_a087554

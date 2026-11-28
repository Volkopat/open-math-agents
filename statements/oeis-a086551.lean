import Mathlib

/-!
# A086551: a(n) = smallest k such that tau(k) = n*tau(k-1) where tau(k) = number of divisors of k, or 0 if no such number exists.

Source: https://oeis.org/A086551
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
Drafted in an earlier generic agent run; audited against the source statement before submission.

Conjectures: (1) No term is zero. (2) a(n)-1 is a prime.
-/

namespace OMA.S_oeis_a086551

noncomputable def a (n : ℕ) : ℕ :=
  sInf {k : ℕ | 2 ≤ k ∧ (Nat.divisors k).card = n * (Nat.divisors (k - 1)).card}

theorem main :
    ∀ n : ℕ, 1 ≤ n →
      (∃ k : ℕ, 2 ≤ k ∧ (Nat.divisors k).card = n * (Nat.divisors (k - 1)).card) ∧
      (a n - 1).Prime := by
  sorry

end OMA.S_oeis_a086551

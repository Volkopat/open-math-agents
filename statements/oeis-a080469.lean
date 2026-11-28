import Mathlib

/-!
# A080469: Composite numbers k such that binomial(3*k, k) == 3^k (mod k)

Source: https://oeis.org/A080469
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
Drafted in an earlier generic agent run; audited against the source statement before submission.

Composite numbers k such that binomial(3*k, k) == 3^k (mod k).
Conjecture: There are infinitely many terms of the form 3^k * p where p is prime and k >= 1.
-/

namespace OMA.S_oeis_a080469

theorem main :
    Set.Infinite
      {m : ℕ | 1 < m ∧ ¬ Nat.Prime m ∧ Nat.choose (3 * m) m ≡ 3 ^ m [MOD m] ∧
        ∃ k : ℕ, 1 ≤ k ∧ ∃ p : ℕ, Nat.Prime p ∧ m = 3 ^ k * p} := by
  sorry

end OMA.S_oeis_a080469

import Mathlib

/-!
# A077028: Primes in every row of the rascal triangle except rows 0, 1, 6, 30, and 54

Source: https://oeis.org/A077028
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
Drafted in an earlier generic agent run; audited against the source statement before submission.

Title: A077028: The rascal triangle, read by rows: T(n,k) (n >= 0, 0 <= k <= n) = k(n-k) + 1.

Statement:
Conjecture: every row except rows 0, 1, 6, 30, and 54 contains a prime.
-/

namespace OMA.S_oeis_a077028

theorem main :
    ∀ n : ℕ, n ≠ 0 → n ≠ 1 → n ≠ 6 → n ≠ 30 → n ≠ 54 →
      ∃ k : ℕ, k ≤ n ∧ Nat.Prime (k * (n - k) + 1) := by
  sorry

end OMA.S_oeis_a077028

import Mathlib

/-!
# A049048: Uniqueness of n >= 2 with n! == 1 (mod c) for composite c

Source: https://oeis.org/A049048
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
Drafted in an earlier generic agent run; audited against the source statement before submission.

Title: A049048: Composite numbers n such that k! == 1 (mod n) for some k > 2.

Statement:
Conjecture: If c is composite then n! == 1 (mod c) for at most one n >= 2.
-/

namespace OMA.S_oeis_a049048

theorem main :
    ∀ c : ℕ, 1 < c → ¬ Nat.Prime c →
      ∀ n₁ n₂ : ℕ, 2 ≤ n₁ → 2 ≤ n₂ →
        n₁.factorial % c = 1 → n₂.factorial % c = 1 → n₁ = n₂ := by
  sorry

end OMA.S_oeis_a049048

import Mathlib

/-!
# A071558: Upper bound sqrt(n)*log(n) on smallest k with n*k - 1 and n*k + 1 twin primes

Source: https://oeis.org/A071558
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
-- Draft from an earlier generic agent run; audited against the source and checked by this agent.

Title: A071558: Smallest k such that n*k + 1 and n*k - 1 are twin primes.

Statement:
Conjecture: a(n) < sqrt(n) * log(n) for all n > 17261.
-/

namespace OMA.S_oeis_a071558

/-- Smallest positive integer `k` such that `n*k - 1` and `n*k + 1` are both prime. -/
noncomputable def a (n : ℕ) : ℕ :=
  sInf {k : ℕ | 1 ≤ k ∧ Nat.Prime (n * k - 1) ∧ Nat.Prime (n * k + 1)}

theorem main :
    ∀ n : ℕ, 17261 < n →
      (∃ k : ℕ, 1 ≤ k ∧ Nat.Prime (n * k - 1) ∧ Nat.Prime (n * k + 1)) ∧
      (a n : ℝ) < Real.sqrt (n : ℝ) * Real.log (n : ℝ) := by
  sorry

end OMA.S_oeis_a071558

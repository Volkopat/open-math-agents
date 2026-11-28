import Mathlib

/-!
# OEIS A047949: Largest m such that n - m and n + m are both primes

Source: https://oeis.org/A047949
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
Drafted in an earlier generic agent run; audited against the source statement before submission.

Conjecture (Goldbach): For every integer `n ≥ 2`, there exists `m ≤ n`
such that `n - m` and `n + m` are both prime (so `a(n) ≥ 0`).
-/

namespace OMA.S_oeis_a047949

theorem main :
    ∀ n : ℕ, 2 ≤ n →
      ∃ m : ℕ, m ≤ n ∧ Nat.Prime (n - m) ∧ Nat.Prime (n + m) := by
  sorry

end OMA.S_oeis_a047949

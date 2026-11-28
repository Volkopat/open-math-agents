import Mathlib

/-!
# A089348: Primes of the form smallest multiple of n followed by a 1

Source: https://oeis.org/A089348
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
-- Draft from an earlier generic agent run; audited against the source and checked by this agent.

Primes of the form smallest multiple of n followed by a 1.
Conjecture: (a(n) - 1) / (10 * n) < n, or a(n) < 10 * n^2 + 1, for all n > 2.
-/

namespace OMA.S_oeis_a089348

/-- Smallest prime of the form 10 * (k * n) + 1 with k > 0. -/
noncomputable def a (n : ℕ) : ℕ :=
  sInf {p : ℕ | Nat.Prime p ∧ ∃ k : ℕ, 0 < k ∧ p = 10 * k * n + 1}

theorem main :
    ∀ n : ℕ, 2 < n → a n < 10 * n ^ 2 + 1 := by
  sorry

end OMA.S_oeis_a089348

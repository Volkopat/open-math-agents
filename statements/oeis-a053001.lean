import Mathlib

/-!
# OEIS A053001: Largest prime < n^2 (Legendre's conjecture)

Source: https://oeis.org/A053001
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
Drafted in an earlier generic agent run; audited against the source statement before submission.

Let `a(n)` be the largest prime strictly less than `n^2`.

Conjecture (Legendre's conjecture): For every `n ≥ 2`, `a(n) > (n - 1)^2`
(equivalently, there is always a prime strictly between `(n - 1)^2` and `n^2`).
-/

namespace OMA.S_oeis_a053001

noncomputable def largestPrimeBelowSq (n : ℕ) : ℕ :=
  sSup { p : ℕ | Nat.Prime p ∧ p < n ^ 2 }

theorem main :
    ∀ n : ℕ, 2 ≤ n → (n - 1) ^ 2 < largestPrimeBelowSq n := by
  sorry

end OMA.S_oeis_a053001

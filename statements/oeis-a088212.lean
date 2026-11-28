import Mathlib

/-!
# OEIS A088212: smallest k > 1 with n + k² prime takes every value

Source: https://oeis.org/A088212
`a n` is the smallest `k > 1` such that `n + k²` is prime. Conjecture: every integer `> 1`
eventually appears as a value.

Conventions. `n ≥ 1`.

-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
-/

namespace OMA.S_oeis_a088212

/-- A088212. -/
noncomputable def a (n : ℕ) : ℕ := sInf {k | 1 < k ∧ (n + k ^ 2).Prime}

theorem main : ∀ m : ℕ, 1 < m → ∃ n : ℕ, 1 ≤ n ∧ a n = m := by
  sorry

end OMA.S_oeis_a088212

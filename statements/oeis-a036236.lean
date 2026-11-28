import Mathlib

/-!
# A036236: Graham's conjecture on `2^k mod k`

Source: https://oeis.org/A036236
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

Conjecture (Ron Graham, 1960, listed in A036236): for any `n > 1` there are infinitely many
solutions `k` of `2^k mod k = n`.
-/

namespace OMA.S_oeis_a036236

theorem main : ∀ n : ℕ, 1 < n → {k : ℕ | 0 < k ∧ 2 ^ k % k = n}.Infinite := by
  sorry

end OMA.S_oeis_a036236

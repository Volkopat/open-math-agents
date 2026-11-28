import Mathlib

/-!
# OEIS A078506: transcendence of ∑ 1/p(n)

Source: https://oeis.org/A078506
The constant `∑_{n ≥ 0} 1/p(n)`, `p` the unrestricted partition function. Conjecture
(Zhi-Wei Sun, 2023): this is a transcendental number.

Conventions. `p(n)` is the number of partitions of `n` (`Fintype.card (Nat.Partition n)`).

-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
-/

namespace OMA.S_oeis_a078506

theorem main :
    Transcendental ℚ (∑' n : ℕ, 1 / (Fintype.card (Nat.Partition n) : ℝ)) := by
  sorry

end OMA.S_oeis_a078506

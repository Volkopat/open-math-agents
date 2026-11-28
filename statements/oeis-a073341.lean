import Mathlib

/-!
# A073341: Iterating x -> x * ceiling(x) starting from (2n+1)/4

Source: https://oeis.org/A073341
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
-- Draft from an earlier generic agent run; audited against the source and checked by this agent.

Number of steps to reach an integer starting with (2n+1)/4 and iterating the map
x -> x * ceiling(x).
Conjecture: An integer is always reached.
The entry has offset 2: for n = 0, 1 the start 1/4, 3/4 is a fixed point of the map.
-/

namespace OMA.S_oeis_a073341

/-- The iteration step `x ↦ x * ⌈x⌉` on `ℚ`. -/
def step (x : ℚ) : ℚ :=
  x * (Int.ceil x : ℚ)

theorem main :
    ∀ n : ℕ, 2 ≤ n → ∃ k : ℕ, ∃ m : ℤ, step^[k] ((2 * (n : ℚ) + 1) / 4) = (m : ℚ) := by
  sorry

end OMA.S_oeis_a073341

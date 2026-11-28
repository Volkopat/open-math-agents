import Mathlib

/-!
# Triangular factorials (OEIS A338489)

Source: https://oeis.org/A338489
Credit: @yuka30240
-/

namespace OMA.S_oeis_a338489

/-- The factorials at indices 0, 1, 3 and 5 are exactly the triangular factorials. -/
theorem main : ∀ n : ℕ,
    (∃ k : ℕ, n.factorial = k * (k + 1) / 2) ↔
      n = 0 ∨ n = 1 ∨ n = 3 ∨ n = 5 := by
  sorry

end OMA.S_oeis_a338489

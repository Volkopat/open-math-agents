import Mathlib

/-!
# OEIS A002063

Source: https://oeis.org/A002063 (OEIS Foundation, CC BY-SA 4.0).
Credit: @Ciphore

The entry conjectures that the squares expressible as the sum of exactly two distinct
powers of two are precisely the terms `9 * 4^n`.
-/

namespace OMA.S_oeis_a002063

theorem main : ∀ x : ℕ,
    (∃ i j : ℕ, i < j ∧ x ^ 2 = 2 ^ i + 2 ^ j) ↔
      ∃ n : ℕ, x ^ 2 = 9 * 4 ^ n := by
  sorry

end OMA.S_oeis_a002063

import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Data.Int.Basic

/-! Source: https://mathoverflow.net/questions/432432 -/

namespace OMA.S_mo_432432

theorem main :
    ∀ z : ℤ, (∀ p : ℕ, p.Prime → (p : ℤ) ∣ z ^ 3 + 1 → (p : ℤ) ^ 2 ∣ z ^ 3 + 1) ↔
      z = -1 ∨ z = 0 ∨ z = 2 ∨ z = 23 := by
  sorry

end OMA.S_mo_432432

import Mathlib

/-!
# MathOverflow 349002

Source: https://mathoverflow.net/questions/349002
-/

namespace OMA.S_mo_349002

open Set

theorem main : ∀ q : ℕ, Odd q → 1<q →
      ∃ r : ℝ, 1<r ∧ (r : ℂ)^q-(r : ℂ)^(q-2)-1=0 ∧
        ∀ z : ℂ, z^q-z^(q-2)-1=0 → z≠(r : ℂ) → ‖z‖<r := by
  sorry

end OMA.S_mo_349002

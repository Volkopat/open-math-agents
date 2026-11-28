import Mathlib

/-!
# MathOverflow 219776

Source: https://mathoverflow.net/questions/219776
-/

namespace OMA.S_mo_219776

open Set

theorem main : ∀ (α : ℝ), 0 < α → ∀ h f g : ℝ → ℝ,
      ContinuousOn h (Icc 0 α) →
      (∃ y ∈ Icc 0 α, h y ≠ 1) →
      ContinuousOn f (Icc 0 α) → MonotoneOn f (Icc 0 α) → f 0 = 0 →
      (∀ x ∈ Icc 0 α, ∀ y ∈ Icc 0 α, h y * x + y ∈ Icc 0 α →
        f (h y * x + y) = g y * f x + f y) →
      ∃ c : ℝ, ∀ x ∈ Icc 0 α, f x = c * x := by
  sorry

end OMA.S_mo_219776

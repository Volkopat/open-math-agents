import Mathlib

/-!
# MathOverflow 434426

Source: https://mathoverflow.net/questions/434426
-/

namespace OMA.S_mo_434426

/-- Nat indices represent the positive integers m+1 and n+1 in the series. -/
noncomputable def scale (a : ℝ) (m : ℕ) : ℝ := a ^ (m+1) / (↑(m+1) : ℝ)

noncomputable def term (a : ℝ) (m n : ℕ) : ℝ :=
  1 / (scale a m * (scale a m + scale a n))

theorem main : ∀ a : ℝ, 1 < a →
    (∑' m : ℕ, ∑' n : ℕ, term a m n) = a^2/(2*(a-1)^4) := by
  sorry

end OMA.S_mo_434426

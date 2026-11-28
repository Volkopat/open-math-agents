import Mathlib

/-!
# A uniform inequality for four trigonometric factors

Source: MO B, https://mathoverflow.net/questions/421887
Credit: @connoranderson
-/

namespace OMA.S_mo_421887

theorem main : ∀ t x : ℝ, t ∈ Set.Icc (0 : ℝ) 1 →
    let z₀ := 1 - 4 * t * (1 - t) * Real.sin (4 * x) ^ 2
    let z₁ := 1 - 4 * z₀ * (1 - z₀) * Real.sin (3 * x) ^ 2
    256 * t * (1 - t) * z₀ * z₁ *
      (Real.sin x * Real.sin (2*x) * Real.sin (3*x) * Real.sin (4*x)) ^ 2 < 3/2 := by
  sorry

end OMA.S_mo_421887

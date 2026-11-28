import Mathlib

/-!
# MathOverflow 309202

Source: https://mathoverflow.net/questions/309202
-/

namespace OMA.S_mo_309202

open Set

theorem main : ∀ (X : Type) [UniformSpace X],
    (∀ f : X → ℝ, Continuous f → (∃ C : ℝ, ∀ x, |f x| ≤ C) → UniformContinuous f) →
    ∀ f : X → ℝ, Continuous f → UniformContinuous f := by
  sorry

end OMA.S_mo_309202

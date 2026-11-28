import Mathlib

/-!
# MathOverflow 225439

Source: https://mathoverflow.net/questions/225439
-/

namespace OMA.S_mo_225439

open Set Matrix
open scoped BigOperators

def radialPlaneSupports {d : ℕ} (H : Set (Fin d → ℝ)) (p : Fin d → ℝ) : Prop :=
  (∀ x ∈ H, p ⬝ᵥ x ≤ p ⬝ᵥ p) ∨ ∀ x ∈ H, p ⬝ᵥ p ≤ p ⬝ᵥ x

theorem main : ∀ (d : ℕ) (S : Finset (Fin d → ℝ)),
      let H := convexHull ℝ (S : Set (Fin d → ℝ))
      H ⊆ stdSimplex ℝ (Fin d) →
        ∀ p ∈ H.extremePoints ℝ, radialPlaneSupports H p := by
  sorry

end OMA.S_mo_225439

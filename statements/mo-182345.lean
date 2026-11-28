import Mathlib

/-!
# MathOverflow 182345

Source: https://mathoverflow.net/questions/182345
-/

namespace OMA.S_mo_182345

open MeasureTheory

theorem main : ∀ (X : Type) [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    [Lattice X] [IsOrderedAddMonoid X] [PosSMulMono ℝ X],
    (∀ x y : X, |x| ≤ |y| → ‖x‖ ≤ ‖y‖) →
    ∀ Z : ℝ → (X →L[ℝ] X), Z 0 = ContinuousLinearMap.id ℝ X →
    (∀ t u : ℝ, 0 ≤ t → 0 ≤ u → Z (t + u) = (Z t).comp (Z u)) →
    (∀ t : ℝ, 0 ≤ t → ∀ x : X, 0 ≤ x → 0 ≤ Z t x) →
    ∀ f : X, 0 ≤ f →
    IntervalIntegrable (fun s : ℝ => Z (1 - s) f + Z (1 + s) f) volume 0 1 →
    0 ≤ (∫ s in (0 : ℝ)..1, Z (1 - s) f + Z (1 + s) f) - f := by
  sorry

end OMA.S_mo_182345

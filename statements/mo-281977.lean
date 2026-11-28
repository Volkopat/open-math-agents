import Mathlib

/-!
# MathOverflow 281977

Source: https://mathoverflow.net/questions/281977
-/

namespace OMA.S_mo_281977

open Set Metric
open scoped InnerProductSpace

def PositivePoissonOnUnitBall (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (w : E → ℝ) : Prop :=
  ContDiffOn ℝ 2 w (ball 0 1) ∧ ∀ x ∈ ball (0 : E) 1, 0 < w x ∧ InnerProductSpace.laplacianWithin w Set.univ x = 1

theorem main : (∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
        [FiniteDimensional ℝ E] (w : E → ℝ), PositivePoissonOnUnitBall E w →
      ∃ C : ℝ, 0 < C ∧ ∀ y ∈ ball (0 : E) (1/2), C*w 0 ≤ w y) ∧
    (¬ (∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
        [FiniteDimensional ℝ E],
      ∃ C : ℝ, 0 < C ∧ ∀ w : E → ℝ, PositivePoissonOnUnitBall E w →
        ∀ y ∈ ball (0 : E) (1/2), C*w 0 ≤ w y)) := by
  sorry

end OMA.S_mo_281977

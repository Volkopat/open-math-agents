import Mathlib

/-!
# MathOverflow 143188

Source: https://mathoverflow.net/questions/143188
-/

namespace OMA.S_mo_143188

open Set Topology

theorem main : ∀ (E : Type) [AddCommGroup E] [Module ℝ E]
    [UniformSpace E] [IsUniformAddGroup E] [T2Space E] [TopologicalSpace.MetrizableSpace E]
    [CompleteSpace E] [TopologicalSpace.SeparableSpace E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E],
    ¬ FiniteDimensional ℝ E →
      ¬ ∃ U : Set E, IsOpen U ∧ Nonempty ((ℕ → Circle) ≃ₜ U) := by
  sorry

end OMA.S_mo_143188

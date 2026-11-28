import Mathlib

/-!
# MathOverflow 156321

Source: https://mathoverflow.net/questions/156321
-/

namespace OMA.S_mo_156321

open Set Filter TopologicalSpace
open scoped Topology ENNReal

theorem main : ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] [SeparableSpace E] (A : Set E),
    IsCompact A → IsCompact (convexHull ℝ A) := by
  sorry

end OMA.S_mo_156321

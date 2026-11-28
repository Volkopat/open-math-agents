import Mathlib

/-!
# MathOverflow 150061

Source: https://mathoverflow.net/questions/150061
-/

namespace OMA.S_mo_150061

open Set Filter
open scoped Topology

def AccumulationOfOrbits (G X : Type) [Group G] [TopologicalSpace X]
    [MulAction G X] : Set X :=
  {x | ∃ (base : X) (s : ℕ → X), Function.Injective s ∧
    (∀ n, ∃ g : G, g • base = s n) ∧ Tendsto s atTop (𝓝 x)}

theorem main : ∀ (G X : Type) [Group G] [TopologicalSpace G] [DiscreteTopology G]
    [MetricSpace X] [CompactSpace X] [MulAction G X] [ContinuousSMul G X],
    IsClosed (AccumulationOfOrbits G X) := by
  sorry

end OMA.S_mo_150061

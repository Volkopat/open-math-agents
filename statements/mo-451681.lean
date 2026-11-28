import Mathlib

/-!
# MathOverflow 451681

Source: https://mathoverflow.net/questions/451681
-/

namespace OMA.S_mo_451681

open Set
open scoped Topology Manifold ContDiff

theorem main : ∀ (E E' : Type) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup E'] [NormedSpace ℝ E']
    [FiniteDimensional ℝ E'] (M N : Type)
    [TopologicalSpace M] [T2Space M] [SecondCountableTopology M] [ChartedSpace E M]
    [IsManifold (𝓘(ℝ,E)) ω M]
    [TopologicalSpace N] [T2Space N] [SecondCountableTopology N] [ChartedSpace E' N]
    [IsManifold (𝓘(ℝ,E')) ω N] [MeasurableSpace N] [BorelSpace N],
    ∀ f : M → N, ContMDiff (𝓘(ℝ,E)) (𝓘(ℝ,E')) ω f →
      ∀ U : Set M, IsOpen U → MeasurableSet (f '' U) := by
  sorry

end OMA.S_mo_451681

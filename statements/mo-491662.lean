import Mathlib

namespace OMA.S_mo_491662

/-- A compact metric space whose connected components are arcs
can be embedded in the plane. -/
theorem main :
    ∀ (X : Type) [MetricSpace X] [CompactSpace X],
      (∀ x : X, Nonempty (connectedComponent x ≃ₜ Set.Icc (0 : ℝ) 1)) →
      ∃ f : X → ℝ × ℝ, Topology.IsEmbedding f := by
  sorry

end OMA.S_mo_491662

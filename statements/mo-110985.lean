import Mathlib

open scoped Manifold ContDiff

namespace OMA.S_mo_110985

abbrev SphereTwo :=
  ↥(Metric.sphere (0 : EuclideanSpace ℝ (Fin (2 + 1))) 1)

abbrev ChartModel := ModelProd (EuclideanSpace ℝ (Fin 2)) (EuclideanSpace ℝ (Fin 2))

noncomputable abbrev SmoothModel := (𝓡 2).prod (𝓡 2)

/-- Does the product of two 2-spheres have an exotic smooth structure? -/
theorem main :
    ∃ (M : Type) (topology : TopologicalSpace M),
      letI := topology
      ∃ atlas : ChartedSpace ChartModel M,
        letI := atlas
        IsManifold SmoothModel ∞ M ∧
          Nonempty (M ≃ₜ (SphereTwo × SphereTwo)) ∧
          ¬ Nonempty (Diffeomorph SmoothModel SmoothModel M (SphereTwo × SphereTwo) ∞) := by
  sorry

end OMA.S_mo_110985

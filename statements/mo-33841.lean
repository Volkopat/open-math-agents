import Mathlib

open scoped Manifold ContDiff

namespace OMA.S_mo_33841

abbrev Euclidean (n : ℕ) := EuclideanSpace ℝ (Fin n)

/-- An exotic smooth four-dimensional Euclidean space has no smooth
product decomposition into a real line and a smooth three-manifold. -/
theorem main :
    ∀ (M : Type) [TopologicalSpace M] [ChartedSpace (Euclidean 4) M]
      [IsManifold (𝓡 4) ∞ M],
      Nonempty (M ≃ₜ Euclidean 4) →
      ¬ Nonempty (Diffeomorph (𝓡 4) (𝓡 4) M (Euclidean 4) ∞) →
      ∀ (N : Type) [TopologicalSpace N] [ChartedSpace (Euclidean 3) N]
        [IsManifold (𝓡 3) ∞ N],
        ¬ Nonempty (Diffeomorph (𝓡 4) ((𝓘(ℝ, ℝ)).prod (𝓡 3)) M (ℝ × N) ∞) := by
  sorry

end OMA.S_mo_33841

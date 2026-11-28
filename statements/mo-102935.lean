import Mathlib

namespace OMA.S_mo_102935

abbrev Space (d : ℕ) := EuclideanSpace ℝ (Fin d)

/-- The facets are the nonempty exposed faces of codimension one. -/
def facets {d : ℕ} (P : Set (Space d)) : Set (Set (Space d)) :=
  {F | F.Nonempty ∧ IsExposed ℝ P F ∧
    Module.finrank ℝ (affineSpan ℝ F).direction = d - 1}

/-- Kalai's weak form of Borsuk's conjecture, with the number of covering
sets given by the number of facets of the polytope. -/
theorem main :
    ∀ d : ℕ, 0 < d → ∀ vertices : Finset (Space d),
      let P := convexHull ℝ (vertices : Set (Space d))
      affineSpan ℝ P = ⊤ →
        ∃ cover : Fin (facets P).ncard → Set (Space d),
          P ⊆ ⋃ i, cover i ∧ ∀ i, Metric.ediam (cover i) < Metric.ediam P := by
  sorry

end OMA.S_mo_102935

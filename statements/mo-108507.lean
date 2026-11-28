import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

open MeasureTheory

namespace OMA.S_mo_108507

abbrev Plane := EuclideanSpace ℝ (Fin 2)

/-- The one-circle version of the annulus problem for Lebesgue measurable complements. -/
theorem main :
    ∀ S : Set Plane, NullMeasurableSet Sᶜ volume →
      (∀ (x : Plane) (ε : ℝ), 0 < ε →
        ∃ r : ℝ, 0 < r ∧ r ∈ Set.Icc (1 - ε) 1 ∧ Metric.sphere x r ⊆ S) →
          volume Sᶜ = 0 := by
  sorry

end OMA.S_mo_108507

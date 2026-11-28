import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Measure.Hausdorff

namespace OMA.S_mo_294882

open MeasureTheory
open scoped ENNReal

abbrev Space (n : ℕ) := EuclideanSpace ℝ (Fin n)

/-- Euclidean volume of the unit ball in the specified dimension. -/
noncomputable def unitBallVolume (n : ℕ) : ℝ≥0∞ :=
  volume (Metric.closedBall (0 : Space n) 1)

/-- The sharp isoperimetric inequality for a compact set, using its topological boundary.
The unit-ball factor converts the diameter convention to normalized Hausdorff measure. -/
theorem main :
    ∀ (n : ℕ), 2 ≤ n →
      ∀ K : Set (Space n), IsCompact K →
        (n : ℝ≥0∞) * (unitBallVolume n) ^ (1 / (n : ℝ)) *
            (volume K) ^ (((n : ℝ) - 1) / (n : ℝ)) ≤
          (unitBallVolume (n - 1) / (2 : ℝ≥0∞) ^ (n - 1)) *
            Measure.hausdorffMeasure ((n : ℝ) - 1) (frontier K) := by
  sorry

end OMA.S_mo_294882

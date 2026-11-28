import Mathlib.Analysis.Convex.Hull
import Mathlib.LinearAlgebra.AffineSpace.Independent
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

open MeasureTheory

namespace OMA.S_mo_133777

abbrev Plane := EuclideanSpace ℝ (Fin 2)

/-- A dissection into equal-area nondegenerate triangles, with shared boundaries allowed. -/
def HasEquidissection (P : Set Plane) (n : ℕ) : Prop :=
  ∃ vertices : Fin n → Fin 3 → Plane,
    let triangle : Fin n → Set Plane := fun i => convexHull ℝ (Set.range (vertices i))
    (∀ i, AffineIndependent ℝ (vertices i)) ∧
      P = (⋃ i, triangle i) ∧
        (∀ ⦃i j⦄, i ≠ j → Disjoint (interior (triangle i)) (interior (triangle j))) ∧
          (∀ i j, volume (triangle i) = volume (triangle j))

/-- The proposed closure of the equidissection spectrum under addition. -/
theorem main :
    ∀ P : Set Plane, Nonempty (P ≃ₜ Metric.closedBall (0 : Plane) 1) →
      ∀ (m n : ℕ), 0 < m → 0 < n →
        HasEquidissection P m → HasEquidissection P n → HasEquidissection P (m + n) := by
  sorry

end OMA.S_mo_133777

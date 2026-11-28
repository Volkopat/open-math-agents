import Mathlib

/-!
# Convex 'fair' partitions of convex polygons

Source: https://www.openproblemgarden.org/op/textbf_convex_fair_partitions_of_convex_polygons
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

Conjecture (Nandakumar–Ramana Rao): every convex polygon allows a convex fair partition into
`n` pieces for every `n`, i.e. a partition into `n` convex pieces all of the same area and
the same perimeter.

Conventions.
* A convex polygon is the convex hull of a finite set of points of the plane, with nonempty
  interior.
* A partition into `n` pieces: compact convex sets `Q₁, …, Qₙ` with pairwise disjoint
  interiors whose union is the polygon (the standard meaning for dissections; boundaries are
  shared).
* Area is Lebesgue measure; the perimeter of a piece is the 1-dimensional Hausdorff measure of
  its boundary. `n ≥ 1`.
-/

namespace OMA.S_opg_textbf_convex_fair_partitions_of_convex_polygons

open MeasureTheory

/-- The plane. -/
abbrev Plane := EuclideanSpace ℝ (Fin 2)

/-- Perimeter of a planar set: length of its boundary. -/
noncomputable def perimeter (Q : Set Plane) : ENNReal :=
  Measure.hausdorffMeasure 1 (frontier Q)

/-- The conjecture. -/
theorem main :
    ∀ (S : Finset Plane), (interior (convexHull ℝ (S : Set Plane))).Nonempty →
      ∀ n : ℕ, 1 ≤ n →
        ∃ Q : Fin n → Set Plane,
          (∀ i, IsCompact (Q i) ∧ Convex ℝ (Q i)) ∧
          (∀ i j, i ≠ j → Disjoint (interior (Q i)) (interior (Q j))) ∧
          (⋃ i, Q i) = convexHull ℝ (S : Set Plane) ∧
          (∀ i j, volume (Q i) = volume (Q j)) ∧
          (∀ i j, perimeter (Q i) = perimeter (Q j)) := by
  sorry

end OMA.S_opg_textbf_convex_fair_partitions_of_convex_polygons

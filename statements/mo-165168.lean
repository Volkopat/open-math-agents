import Mathlib

/-!
# The three-dimensional Japanese theorem question

Source https://mathoverflow.net/q/165168

The question asks whether the sum of the inradii is independent of the
tetrahedralization of a convex polyhedron with cospherical vertices.
Tetrahedralizations here use the original vertices and meet face to face.
-/

open scoped BigOperators

namespace OMA.S_mo_165168

abbrev Point := EuclideanSpace ℝ (Fin 3)
abbrev Tetrahedron := Affine.Simplex ℝ Point 3

def region (t : Tetrahedron) : Set Point :=
  convexHull ℝ (Set.range t.points)

/-- The cells cover the polyhedron. Distinct cells have distinct vertex sets
and meet along the face spanned by their common vertices. -/
def IsTetrahedralization (vertices : Finset Point) (cells : Finset Tetrahedron) : Prop :=
  (∀ t ∈ cells, Set.range t.points ⊆ (vertices : Set Point)) ∧
  (⋃ t ∈ cells, region t) = convexHull ℝ (vertices : Set Point) ∧
  ∀ t ∈ cells, ∀ u ∈ cells, t ≠ u →
    Set.range t.points ≠ Set.range u.points ∧
    region t ∩ region u = convexHull ℝ (Set.range t.points ∩ Set.range u.points)

theorem main :
    ∀ (vertices : Finset Point),
      (∃ (center : Point) (radius : ℝ), (vertices : Set Point) ⊆ Metric.sphere center radius) →
      (interior (convexHull ℝ (vertices : Set Point))).Nonempty →
      ∀ (T U : Finset Tetrahedron),
        IsTetrahedralization vertices T → IsTetrahedralization vertices U →
        (∑ t ∈ T, t.inradius) = ∑ u ∈ U, u.inradius := by
  sorry

end OMA.S_mo_165168

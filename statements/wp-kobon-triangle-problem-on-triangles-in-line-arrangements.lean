import Mathlib

/-!
# Kobon triangle problem

Determine the largest number of triangular faces of an arrangement of `k`
distinct real affine lines in the Euclidean plane. A face is a connected
component of the complement of the lines. Triangles have positive area and
can share boundary edges or vertices. Parallel and concurrent lines are allowed.

Source: https://en.wikipedia.org/wiki/Kobon_triangle_problem
Reference: https://arxiv.org/abs/2507.07951
Credit: @ZenithRains
-/

namespace OMA.S_wp_kobon_triangle_problem_on_triangles_in_line_arrangements

abbrev Plane := EuclideanSpace ℝ (Fin 2)
abbrev Line := AffineSubspace ℝ Plane

/-- An open triangular face of the arrangement. -/
def IsTriangularFace (lines : Finset Line) (face : Set Plane) : Prop :=
  let complement := (⋃ L ∈ lines, (L : Set Plane))ᶜ
  ∃ x ∈ complement, ∃ v : Fin 3 → Plane,
    AffineIndependent ℝ v ∧
      face = connectedComponentIn complement x ∧
      face = interior (convexHull ℝ (Set.range v))

/-- The number of triangular faces realized by an arrangement of `k` lines. -/
def IsAchievableCount (k m : ℕ) : Prop :=
  ∃ lines : Finset Line,
    lines.card = k ∧
      (∀ L ∈ lines, Module.finrank ℝ L.direction = 1) ∧
      {face | IsTriangularFace lines face}.encard = m

/-- Find the sequence of greatest achievable counts. -/
theorem main : ∃ N : ℕ → ℕ, ∀ k : ℕ,
    IsGreatest {m | IsAchievableCount k m} (N k) := by
  sorry

end OMA.S_wp_kobon_triangle_problem_on_triangles_in_line_arrangements

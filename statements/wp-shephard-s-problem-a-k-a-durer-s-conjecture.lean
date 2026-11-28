import Mathlib

/-!
# Shephard's problem (a.k.a. Dürer's conjecture)

Source: https://en.wikipedia.org/wiki/Shephard%27s_conjecture
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

Shephard's problem (Wikipedia): does every convex polyhedron have a net, i.e. a simple
(non-overlapping) edge unfolding? The expected answer, stated here, is yes.

Conventions:
* A convex polytope is a 3-dimensional one, as in the source: the convex hull of a finite set in
  `ℝ³` with nonempty interior. Its facets (resp. edges) are its nonempty exposed faces of
  dimension 2 (resp. 1).
* An edge unfolding cuts the surface along some edges and flattens it onto the plane without
  distorting the faces: each facet `F` is mapped into the plane by a map that is isometric on
  `F`; the uncut edges form a spanning tree of the dual graph (facets, adjacent when they share
  an edge), and two facets sharing an uncut edge are mapped so that they agree on that edge. (For
  a 3-polytope, the complement of a dual spanning tree is a spanning tree of the 1-skeleton, the
  usual description of the cut set.)
* Non-overlapping: the images of the relative interiors of distinct facets are disjoint.
-/

namespace OMA.S_wp_shephard_s_problem_a_k_a_durer_s_conjecture

open Set

/-- Euclidean 3-space and the plane. -/
abbrev E3 := EuclideanSpace ℝ (Fin 3)
abbrev E2 := EuclideanSpace ℝ (Fin 2)

/-- The faces of `P` of dimension `k`: nonempty exposed faces whose affine span has
dimension `k`. -/
def faces (P : Set E3) (k : ℕ) : Set (Set E3) :=
  {F | IsExposed ℝ P F ∧ F.Nonempty ∧ Module.finrank ℝ (vectorSpan ℝ F) = k}

/-- `P` has a non-overlapping edge unfolding. -/
def HasNonOverlappingEdgeUnfolding (P : Set E3) : Prop :=
  ∃ (U : Set (Set E3)) (φ : Set E3 → E3 → E2),
    U ⊆ faces P 1 ∧
    -- the uncut edges form a spanning tree of the dual graph
    (SimpleGraph.fromRel (fun F G : faces P 2 => (F : Set E3) ∩ G ∈ U)).IsTree ∧
    -- each facet is unfolded isometrically
    (∀ F ∈ faces P 2, ∀ x ∈ F, ∀ y ∈ F, dist (φ F x) (φ F y) = dist x y) ∧
    -- facets sharing an uncut edge stay glued along it
    (∀ F ∈ faces P 2, ∀ G ∈ faces P 2, F ∩ G ∈ U → ∀ x ∈ F ∩ G, φ F x = φ G x) ∧
    -- no overlap
    (∀ F ∈ faces P 2, ∀ G ∈ faces P 2, F ≠ G →
      Disjoint (φ F '' intrinsicInterior ℝ F) (φ G '' intrinsicInterior ℝ G))

theorem main :
    ∀ S : Finset E3, (interior (convexHull ℝ (S : Set E3))).Nonempty →
      HasNonOverlappingEdgeUnfolding (convexHull ℝ (S : Set E3)) := by
  sorry

end OMA.S_wp_shephard_s_problem_a_k_a_durer_s_conjecture

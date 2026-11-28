import Mathlib

/-!
# Dense rational distance sets in the plane

Source: https://www.openproblemgarden.org/op/dense_rational_distance_sets_in_the_plane
Asked by Ulam, who guessed that the answer is negative: is there a dense set of points of the
plane such that all pairwise distances between its points are rational numbers?

This states the question exactly as the source asks it: existence of a dense subset of the
Euclidean plane all of whose pairwise distances are rational.
-/

namespace OMA.S_opg_dense_rational_distance_sets_in_the_plane

/-- Ulam's problem: there is a dense set of points of the plane such that the distance between
any two distinct points of the set is a rational number. -/
theorem main :
    ∃ S : Set (EuclideanSpace ℝ (Fin 2)),
      Dense S ∧ ∀ x ∈ S, ∀ y ∈ S, x ≠ y → ∃ q : ℚ, dist x y = (q : ℝ) := by
  sorry

end OMA.S_opg_dense_rational_distance_sets_in_the_plane

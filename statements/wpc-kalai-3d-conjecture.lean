import Mathlib

/-!
# Kalai's 3^d conjecture

Source: https://en.wikipedia.org/wiki/Kalai%27s_3%5Ed_conjecture
Credit: @pyaf (agent: Claude Code, model claude-opus-5-5)

Source statement (Kalai, 1989): every `d`-dimensional centrally symmetric polytope has at least
`3^d` nonempty faces (including the polytope itself as a face but not including the empty set).

Conventions:
* a `d`-dimensional polytope is taken in `ℝ^d = EuclideanSpace ℝ (Fin d)` as the convex hull `P`
  of a finite point set with nonempty interior (any `d`-dimensional polytope is affinely
  isomorphic to one of these, and affine isomorphisms preserve faces and central symmetry);
* centrally symmetric: there is a centre `c` with `2c - x ∈ P` for every `x ∈ P`;
* the nonempty faces of a convex polytope are exactly its nonempty exposed faces, i.e. the sets
  `{x ∈ P | ∀ y ∈ P, l y ≤ l x}` for continuous linear functionals `l` (Mathlib's `IsExposed`);
  `l = 0` gives `P` itself, so `P` is counted, and the empty set is excluded explicitly;
* a polytope has finitely many faces, so `Set.ncard` is the number of nonempty faces.
-/

namespace OMA.S_wpc_kalai_3d_conjecture

/-- The nonempty faces of a convex set `P`: its nonempty exposed subsets. -/
def nonemptyFaces {d : ℕ} (P : Set (EuclideanSpace ℝ (Fin d))) :
    Set (Set (EuclideanSpace ℝ (Fin d))) :=
  {F | F.Nonempty ∧ IsExposed ℝ P F}

/-- **Kalai's 3^d conjecture.** Every `d`-dimensional centrally symmetric polytope has at least
`3^d` nonempty faces. -/
theorem main : ∀ (d : ℕ) (S : Finset (EuclideanSpace ℝ (Fin d))),
    (interior (convexHull ℝ (S : Set (EuclideanSpace ℝ (Fin d))))).Nonempty →
    (∃ c : EuclideanSpace ℝ (Fin d), ∀ x ∈ convexHull ℝ (S : Set (EuclideanSpace ℝ (Fin d))),
      (2 : ℝ) • c - x ∈ convexHull ℝ (S : Set (EuclideanSpace ℝ (Fin d)))) →
    3 ^ d ≤ (nonemptyFaces (convexHull ℝ (S : Set (EuclideanSpace ℝ (Fin d))))).ncard := by
  sorry

end OMA.S_wpc_kalai_3d_conjecture

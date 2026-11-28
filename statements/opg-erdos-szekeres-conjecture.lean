import Mathlib

/-!
# The Erdős–Szekeres conjecture (happy ending problem)

Source: https://www.openproblemgarden.org/op/erdos_szekeres_conjecture

Conjecture: every set of `2 ^ (n - 2) + 1` points of the plane in general position contains `n`
points which form a convex `n`-gon. General position means that no three of the points are
collinear; a finite set of points is in convex position when none of its points lies in the
convex hull of the others, which for points in general position is the same as saying that they
are the vertices of a convex polygon.
-/

namespace OMA.S_opg_erdos_szekeres_conjecture

/-- No three points of `S` are collinear: `S` is in general position. -/
def IsGeneralPosition (S : Finset (EuclideanSpace ℝ (Fin 2))) : Prop :=
  ∀ a ∈ S, ∀ b ∈ S, ∀ c ∈ S, a ≠ b → b ≠ c → a ≠ c →
    ¬ Collinear ℝ ({a, b, c} : Set (EuclideanSpace ℝ (Fin 2)))

/-- Every point of `S` is a vertex of the convex hull of `S`: the points of `S` are in convex
position. -/
def InConvexPosition (S : Finset (EuclideanSpace ℝ (Fin 2))) : Prop :=
  ∀ p ∈ S, p ∉ convexHull ℝ ((↑(S.erase p)) : Set (EuclideanSpace ℝ (Fin 2)))

/-- The Erdős–Szekeres conjecture: any `2 ^ (n - 2) + 1` points of the plane in general position
contain the vertices of a convex `n`-gon. -/
theorem main : ∀ n : ℕ, 3 ≤ n → ∀ S : Finset (EuclideanSpace ℝ (Fin 2)),
    IsGeneralPosition S → 2 ^ (n - 2) + 1 ≤ S.card →
      ∃ T : Finset (EuclideanSpace ℝ (Fin 2)), T ⊆ S ∧ T.card = n ∧ InConvexPosition T := by
  sorry

end OMA.S_opg_erdos_szekeres_conjecture

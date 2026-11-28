import Mathlib

/-!
# Inequality conjecture for convex pentagons

Source: https://math.stackexchange.com/questions/4265952/inequality-conjecture-for-convex-pentagons
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
Drafted in an earlier generic agent run; audited against the source statement before submission.

Let `X_1, ..., X_5` be the vertices of a convex pentagon with perimeter `p` and
centroid at the origin, satisfying `d(X_i, X_j) < p / 3` for all `1 ≤ i, j ≤ 5`,
where `d` is the Euclidean distance. Let `X_m` be a vertex of maximal distance
to the origin and let `P` be the orthogonal projection onto the straight line
through `X_m` and the origin. Conjecture:
`∑_{i=1}^5 d(X_m, P X_i) ≤ (1 / (2 sin(π / 5))) ∑_{i=1}^5 d(X_m, X_i)`.

Conventions:
- Vertices are indexed by `Fin 5` in cyclic order (either counterclockwise or
  clockwise), with strict convexity expressed via consistent cross-product signs
  against every directed edge `X_i → X_{i+1}`.
- The centroid condition is formalized as the vertex centroid `∑ i, X i = 0`.
-/

namespace OMA.S_mse_4265952

abbrev Point2 := EuclideanSpace ℝ (Fin 2)

def cross2 (u v : Point2) : ℝ :=
  u 0 * v 1 - u 1 * v 0

def IsConvexPentagon (X : Fin 5 → Point2) : Prop :=
  (∀ i j : Fin 5, j ≠ i → j ≠ i + 1 → 0 < cross2 (X (i + 1) - X i) (X j - X i)) ∨
  (∀ i j : Fin 5, j ≠ i → j ≠ i + 1 → cross2 (X (i + 1) - X i) (X j - X i) < 0)

noncomputable def perimeter (X : Fin 5 → Point2) : ℝ :=
  ∑ i : Fin 5, dist (X i) (X (i + 1))

noncomputable def projOnto (u v : Point2) : Point2 :=
  (inner ℝ v u / ‖u‖ ^ 2) • u

theorem main :
    ∀ (X : Fin 5 → Point2) (m : Fin 5),
      IsConvexPentagon X →
      (∑ i : Fin 5, X i) = 0 →
      (∀ i j : Fin 5, dist (X i) (X j) < perimeter X / 3) →
      (∀ i : Fin 5, ‖X i‖ ≤ ‖X m‖) →
      ∑ i : Fin 5, dist (X m) (projOnto (X m) (X i)) ≤
        (1 / (2 * Real.sin (Real.pi / 5))) * ∑ i : Fin 5, dist (X m) (X i) := by
  sorry

end OMA.S_mse_4265952

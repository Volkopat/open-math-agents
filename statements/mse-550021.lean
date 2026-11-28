import Mathlib

/-!
# Characterization of convex polygons via inward-pointing rays

Source: https://math.stackexchange.com/questions/550021/characterization-of-convex-polygons
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
-- Draft from an earlier generic agent run; audited against the source and checked by this agent.

Let $P$ be a simple polygon in $\mathbb{R}^2$. A ray emanating from a vertex $v$ of $P$ that
does not pass through any other vertex of $P$ is called inward-pointing if it intersects the
boundary of $P$ (excluding $v$) an odd number of times. A vertex $v$ is called convex if
every inward-pointing ray from $v$ lies in the interior of the angle at $v$.

Prove that if every vertex of $P$ is convex in this sense, then $P$ is a convex polygon
(for each edge, all vertices lie in the same closed half-plane bounded by that edge).
-/

namespace OMA.S_mse_550021

/-- 2D cross product (signed area) of two vectors in $\mathbb{R}^2$. -/
def cross2D (u w : ℝ × ℝ) : ℝ :=
  u.1 * w.2 - u.2 * w.1

/-- Closed line segment between `p` and `q` in $\mathbb{R}^2$. -/
def closedSeg (p q : ℝ × ℝ) : Set (ℝ × ℝ) :=
  {x | ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ x = ((1 - t) * p.1 + t * q.1, (1 - t) * p.2 + t * q.2)}

/-- Open ray starting at `p` (excluding `p`) in direction `u`. -/
def openRay (p u : ℝ × ℝ) : Set (ℝ × ℝ) :=
  {x | ∃ t : ℝ, 0 < t ∧ x = (p.1 + t * u.1, p.2 + t * u.2)}

/-- Boundary of the polygon with cyclic vertex sequence `v : Fin n → ℝ × ℝ`. -/
def polyBoundary {n : ℕ} [NeZero n] (v : Fin n → ℝ × ℝ) : Set (ℝ × ℝ) :=
  ⋃ i : Fin n, closedSeg (v i) (v (i + 1))

/-- `v` defines a simple polygon with non-collinear consecutive vertices. -/
def IsSimplePolygon {n : ℕ} [NeZero n] (v : Fin n → ℝ × ℝ) : Prop :=
  3 ≤ n ∧
  Function.Injective v ∧
  (∀ i : Fin n,
    cross2D ((v (i + 1)).1 - (v i).1, (v (i + 1)).2 - (v i).2)
            ((v (i - 1)).1 - (v i).1, (v (i - 1)).2 - (v i).2) ≠ 0) ∧
  (∀ i j : Fin n, i ≠ j → j ≠ i + 1 → i ≠ j + 1 →
    Disjoint (closedSeg (v i) (v (i + 1))) (closedSeg (v j) (v (j + 1)))) ∧
  (∀ i : Fin n,
    closedSeg (v i) (v (i + 1)) ∩ closedSeg (v (i + 1)) (v (i + 2)) = {v (i + 1)})

/-- A ray from vertex `v i` in direction `u` is inward-pointing. -/
def IsInwardRay {n : ℕ} [NeZero n] (v : Fin n → ℝ × ℝ) (i : Fin n) (u : ℝ × ℝ) : Prop :=
  u ≠ (0, 0) ∧
  (∀ j : Fin n, j ≠ i → v j ∉ openRay (v i) u) ∧
  ∃ S : Finset (ℝ × ℝ), (S : Set (ℝ × ℝ)) = openRay (v i) u ∩ polyBoundary v ∧ Odd S.card

/-- Direction `u` lies in the interior of the angle at vertex `v i`. -/
def InAngleInterior {n : ℕ} [NeZero n] (v : Fin n → ℝ × ℝ) (i : Fin n) (u : ℝ × ℝ) : Prop :=
  ∃ a b : ℝ, 0 < a ∧ 0 < b ∧
    u = (a * ((v (i - 1)).1 - (v i).1) + b * ((v (i + 1)).1 - (v i).1),
         a * ((v (i - 1)).2 - (v i).2) + b * ((v (i + 1)).2 - (v i).2))

/-- Vertex `v i` is convex: every inward-pointing ray from `v i` lies in the angle interior. -/
def IsConvexVertex {n : ℕ} [NeZero n] (v : Fin n → ℝ × ℝ) (i : Fin n) : Prop :=
  ∀ u : ℝ × ℝ, IsInwardRay v i u → InAngleInterior v i u

/-- The polygon is convex: for every edge, all vertices lie in one closed half-plane. -/
def IsConvexPolygon {n : ℕ} [NeZero n] (v : Fin n → ℝ × ℝ) : Prop :=
  ∀ i : Fin n,
    (∀ j : Fin n,
      0 ≤ cross2D ((v (i + 1)).1 - (v i).1, (v (i + 1)).2 - (v i).2)
                  ((v j).1 - (v i).1, (v j).2 - (v i).2)) ∨
    (∀ j : Fin n,
      cross2D ((v (i + 1)).1 - (v i).1, (v (i + 1)).2 - (v i).2)
              ((v j).1 - (v i).1, (v j).2 - (v i).2) ≤ 0)

theorem main :
    ∀ (n : ℕ) [NeZero n] (v : Fin n → ℝ × ℝ),
      IsSimplePolygon v →
      (∀ i : Fin n, IsConvexVertex v i) →
      IsConvexPolygon v := by
  sorry

end OMA.S_mse_550021

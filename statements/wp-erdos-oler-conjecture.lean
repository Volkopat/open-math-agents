import Mathlib

-- Erdős–Oler conjecture: for triangular n, packing n - 1 unit circles in an equilateral triangle
-- requires a triangle of the same size as packing n circles.
-- Source: https://en.wikipedia.org/wiki/Circle_packing_in_an_equilateral_triangle
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

/-!
Source: circle packing in an equilateral triangle asks for the smallest equilateral triangle into
which `n` unit circles can be packed. The Erdős–Oler conjecture: if `n` is a triangular number,
then the optimal packings of `n - 1` and of `n` circles have the same side length.

Conventions:
* A packing of `m` unit circles in a triangle `T` is a family of centres `c : Fin m → ℝ²` with
  every closed unit disk `closedBall (c i) 1` contained in `T` and pairwise distances
  `dist (c i) (c j) ≥ 2` (the open disks are disjoint).
* The equilateral triangle of side `a ≥ 0` is placed with vertices `(0,0)`, `(a,0)`,
  `(a/2, a√3/2)`; position and orientation do not matter, since isometries of the plane preserve
  packings.
* `optSide m` is the infimum of the side lengths `a ≥ 0` admitting a packing of `m` unit circles
  (the set is nonempty, as large triangles hold any `m` circles, and bounded below by `0`).
* Triangular numbers are `n = k (k + 1) / 2`. The case `k = 1` (`n = 1`, packing `0` circles) is
  degenerate, where the infimum is `0`, and is excluded: `k ≥ 2`, i.e. `n ≥ 3`.
-/

namespace OMA.S_wp_erdos_oler_conjecture

/-- The closed equilateral triangle of side `a` with vertices `(0,0)`, `(a,0)`, `(a/2, a√3/2)`. -/
noncomputable def eqTriangle (a : ℝ) : Set (EuclideanSpace ℝ (Fin 2)) :=
  convexHull ℝ {!₂[0, 0], !₂[a, 0], !₂[a / 2, a * Real.sqrt 3 / 2]}

/-- `m` unit circles can be packed into the equilateral triangle of side `a`. -/
def Packs (m : ℕ) (a : ℝ) : Prop :=
  ∃ c : Fin m → EuclideanSpace ℝ (Fin 2), (∀ i, Metric.closedBall (c i) 1 ⊆ eqTriangle a) ∧
    ∀ i j, i ≠ j → 2 ≤ dist (c i) (c j)

/-- The optimal side length for packing `m` unit circles in an equilateral triangle. -/
noncomputable def optSide (m : ℕ) : ℝ := sInf {a : ℝ | 0 ≤ a ∧ Packs m a}

/-- The Erdős–Oler conjecture. -/
theorem main : ∀ k : ℕ, 2 ≤ k → optSide (k * (k + 1) / 2 - 1) = optSide (k * (k + 1) / 2) := by
  sorry

end OMA.S_wp_erdos_oler_conjecture

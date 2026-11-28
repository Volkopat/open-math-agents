import Mathlib

/-!
# Intersections of balls with the sphere are geodesically convex

Source: https://mathoverflow.net/questions/249291
Asked by MathOverflow user Longyearbyen.

Let `S` be the `m`-dimensional unit sphere in `ℝ^{m+1}` and let `B` be a closed ball in
`ℝ^{m+1}` such that `B ∩ S` lies within an open hemisphere of `S`. The question asks: is
`B ∩ S` geodesically convex in `S`?

Translation choices.
* `ℝ^{m+1}` is `EuclideanSpace ℝ (Fin (m + 1))`, with `m ≥ 1` (so that `S` is connected and
  has geodesics); `S` is the set of unit vectors.
* `B` is the closed ball of centre `c` and radius `r`, so `B ∩ S` is
  `{x | ‖x‖ = 1 ∧ ‖x - c‖ ≤ r}`.
* An open hemisphere is `{x ∈ S | 0 < ⟪x, e⟫}` for some vector `e`.
* For two points `x, y` of an open hemisphere (so `y ≠ -x`) the minimizing geodesic of `S`
  from `x` to `y` is the shorter great-circle arc, whose points are the normalized
  combinations `‖α x + β y‖⁻¹ (α x + β y)` with `α, β ≥ 0` not both zero. A subset `K` of
  `S` is geodesically convex when it contains all these points for all `x, y ∈ K`
  (`GeodConvex`).
* `main` is the affirmative answer.
-/

namespace OMA.S_mo_249291

open scoped InnerProductSpace

/-- `K` contains the normalized nonnegative combinations of any two of its points, i.e. the
minimizing great-circle arcs between them. -/
def GeodConvex {m : ℕ} (K : Set (EuclideanSpace ℝ (Fin (m + 1)))) : Prop :=
  ∀ x ∈ K, ∀ y ∈ K, ∀ α β : ℝ, 0 ≤ α → 0 ≤ β → α • x + β • y ≠ 0 →
    ‖α • x + β • y‖⁻¹ • (α • x + β • y) ∈ K

theorem main :
    ∀ m : ℕ, 1 ≤ m → ∀ (c : EuclideanSpace ℝ (Fin (m + 1))) (r : ℝ),
      (∃ e : EuclideanSpace ℝ (Fin (m + 1)), ∀ x : EuclideanSpace ℝ (Fin (m + 1)),
        ‖x‖ = 1 → ‖x - c‖ ≤ r → 0 < ⟪x, e⟫_ℝ) →
      GeodConvex {x : EuclideanSpace ℝ (Fin (m + 1)) | ‖x‖ = 1 ∧ ‖x - c‖ ≤ r} := by
  sorry

end OMA.S_mo_249291

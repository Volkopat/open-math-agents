import Mathlib

/-!
# An inequality with spherical triangles

Source: https://mathoverflow.net/questions/233204
Asked by MathOverflow user Lierre.

Let `ABC` be a spherical triangle on the unit sphere, where the spherical distance `AB`
is `π / 2` and `C ≠ -A`. For `t ∈ [0, 1]` let `B(t)` (resp. `C(t)`) be the point on the
segment `[AB]` (resp. `[AC]`) with `AB(t) = t * AB` (resp. `AC(t) = t * AC`). The question
asks: is it true that `B(t)C(t) ≤ 2 * BC` for every `t ∈ [0, 1]`?

Translation choices.
* The sphere is the unit sphere of `EuclideanSpace ℝ (Fin 3)`; all points are given as
  vectors of norm one.
* The spherical distance between two unit vectors is the unoriented angle between them,
  `InnerProductGeometry.angle`, a number in `[0, π]`.
* The segment `[XY]` of the sphere (for `Y ≠ -X`) is the shorter great-circle arc from `X`
  to `Y`, i.e. the set of unit vectors of the form `α • X + β • Y` with `α, β ≥ 0`; this is
  the predicate `OnArc X Y`. Such an arc contains exactly one point at a prescribed distance
  `s ∈ [0, XY]` from `X`, so quantifying over all points `P` (resp. `Q`) on the arc with the
  prescribed distance from `A` covers exactly the points `B(t)` (resp. `C(t)`).
-/

namespace OMA.S_mo_233204

open InnerProductGeometry

/-- `P` lies on the spherical segment from `X` to `Y`: it is a nonnegative combination of
`X` and `Y` (for unit vectors this is the shorter great-circle arc). -/
def OnArc (X Y P : EuclideanSpace ℝ (Fin 3)) : Prop :=
  ∃ α β : ℝ, 0 ≤ α ∧ 0 ≤ β ∧ P = α • X + β • Y

theorem main :
    ∀ A B C : EuclideanSpace ℝ (Fin 3), ‖A‖ = 1 → ‖B‖ = 1 → ‖C‖ = 1 →
      angle A B = Real.pi / 2 → C ≠ -A →
      ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
      ∀ P Q : EuclideanSpace ℝ (Fin 3), ‖P‖ = 1 → ‖Q‖ = 1 →
        OnArc A B P → OnArc A C Q →
        angle A P = t * angle A B → angle A Q = t * angle A C →
        angle P Q ≤ 2 * angle B C := by
  sorry

end OMA.S_mo_233204

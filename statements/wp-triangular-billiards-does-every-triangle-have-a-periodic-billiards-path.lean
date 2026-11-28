import Mathlib

/-!
# Triangular billiards: does every triangle have a periodic billiard path?

Source: https://en.wikipedia.org/wiki/Triangular_billiards
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

Question: does every triangle have a periodic billiard path? `main` states the positive answer
(the conjecture as the source presents it).

Conventions. A triangle is given by three affinely independent points `v 0, v 1, v 2` of the
plane; side `j` is the segment opposite `v j`. A periodic billiard path is a periodic sequence
of bounce points `q i` (period `k ≥ 1`), each in the relative interior of a side `s i` (so the
path never hits a vertex), with consecutive bounces on different sides (so the connecting
segments run through the triangle), obeying the reflection law at every bounce: the outgoing
direction `q (i+1) - q i` is a positive multiple of the mirror image of the incoming direction
`q i - q (i-1)` in the line of side `s i`.
-/

namespace OMA.S_wp_triangular_billiards_does_every_triangle_have_a_periodic_billiards_path

/-- The plane. -/
abbrev Plane := EuclideanSpace ℝ (Fin 2)

/-- Mirror image of `w` in a line with direction `u`. -/
noncomputable def reflectDir (u w : Plane) : Plane :=
  (2 * inner ℝ w u / inner ℝ u u) • u - w

/-- Endpoints of side `j` (the side opposite `v j`). -/
def sideEnds (v : Fin 3 → Plane) (j : Fin 3) : Plane × Plane := (v (j + 1), v (j + 2))

/-- The triangle `v` has a periodic billiard path. -/
def HasPeriodicBilliardPath (v : Fin 3 → Plane) : Prop :=
  ∃ (k : ℕ) (q : ℕ → Plane) (s : ℕ → Fin 3), 0 < k ∧
    (∀ i, q (i + k) = q i ∧ s (i + k) = s i) ∧
    (∀ i, q i ∈ openSegment ℝ (sideEnds v (s i)).1 (sideEnds v (s i)).2) ∧
    (∀ i, s (i + 1) ≠ s i) ∧
    ∀ i, ∃ t : ℝ, 0 < t ∧
      q (i + 2) - q (i + 1) =
        t • reflectDir ((sideEnds v (s (i + 1))).2 - (sideEnds v (s (i + 1))).1)
          (q (i + 1) - q i)

/-- Every triangle has a periodic billiard path. -/
theorem main : ∀ v : Fin 3 → Plane, AffineIndependent ℝ v → HasPeriodicBilliardPath v := by
  sorry

end OMA.S_wp_triangular_billiards_does_every_triangle_have_a_periodic_billiards_path

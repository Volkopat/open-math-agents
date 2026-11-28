import Mathlib

/-!
# Ulam's packing conjecture

Source: https://en.wikipedia.org/wiki/Ulam%27s_packing_conjecture
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

Conjecture (Ulam): among convex solids in three-dimensional space, the ball has the lowest
optimal packing density: every convex body packs at least as densely as the ball.

Conventions:
* A convex body is a compact convex subset of `ℝ³` with nonempty interior.
* A packing of `K` is a sequence of congruent copies `φᵢ(K)` (`φᵢ` isometries of `ℝ³`, rotations
  and reflections allowed; reflections do not change the optimal density of a convex body's
  packings by more than replacing `K` with its mirror image, which is congruent) with pairwise
  disjoint interiors. A packing has countably many members, so sequences suffice.
* Its (upper) density is `limsup_{R → ∞} vol(⋃ᵢ φᵢ(K) ∩ B(0, R)) / vol(B(0, R))`; the optimal
  packing density of `K` is the supremum over packings.
-/

namespace OMA.S_wp_ulam_s_packing_conjecture_about_the_identity_of_the_worst_packing_convex_solid

open MeasureTheory

/-- Euclidean 3-space. -/
abbrev E := EuclideanSpace ℝ (Fin 3)

/-- `φ` is a packing of `K`. -/
def IsPacking (K : Set E) (φ : ℕ → E ≃ᵢ E) : Prop :=
  ∀ i j, i ≠ j → Disjoint (interior (φ i '' K)) (interior (φ j '' K))

/-- The upper density of a set. -/
noncomputable def upperDensity (A : Set E) : ℝ :=
  Filter.limsup (fun R : ℝ => (volume (A ∩ Metric.ball 0 R)).toReal /
    (volume (Metric.ball (0 : E) R)).toReal) Filter.atTop

/-- The optimal packing density of `K`. -/
noncomputable def packingDensity (K : Set E) : ℝ :=
  sSup {d | ∃ φ : ℕ → E ≃ᵢ E, IsPacking K φ ∧ d = upperDensity (⋃ i, φ i '' K)}

theorem main :
    ∀ K : Set E, IsCompact K → Convex ℝ K → (interior K).Nonempty →
      packingDensity (Metric.closedBall (0 : E) 1) ≤ packingDensity K := by
  sorry

end OMA.S_wp_ulam_s_packing_conjecture_about_the_identity_of_the_worst_packing_convex_solid

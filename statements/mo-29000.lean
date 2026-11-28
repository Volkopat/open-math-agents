import Mathlib

/-!
# Volumes of sets of constant width in high dimensions

Source: https://mathoverflow.net/questions/29000
Question (Schramm, posed by Kalai): is there `ε > 0` such that for every `n > 1` there is a set
`Kₙ ⊆ ℝⁿ` of constant width `1` with `vol Kₙ ≤ (1 - ε)ⁿ Vₙ`, where `Vₙ` is the volume of the
ball of radius `1/2`? `main` states the affirmative answer.

Conventions. A set of constant width `1` is a compact convex set whose support function
satisfies `sup_{x∈K} ⟪x, u⟫ - inf_{x∈K} ⟪x, u⟫ = 1` for every unit vector `u`.

-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
-/

namespace OMA.S_mo_29000

open Metric MeasureTheory

/-- `K` is a convex body of constant width `1`. -/
def ConstantWidthOne {n : ℕ} (K : Set (EuclideanSpace ℝ (Fin n))) : Prop :=
  IsCompact K ∧ Convex ℝ K ∧ K.Nonempty ∧
    ∀ u : EuclideanSpace ℝ (Fin n), ‖u‖ = 1 →
      (⨆ x : K, inner ℝ (x : EuclideanSpace ℝ (Fin n)) u) -
        (⨅ x : K, inner ℝ (x : EuclideanSpace ℝ (Fin n)) u) = 1

theorem main :
    ∃ ε : ℝ, 0 < ε ∧ ∀ n : ℕ, 1 < n →
      ∃ K : Set (EuclideanSpace ℝ (Fin n)), ConstantWidthOne K ∧
        volume K ≤ ENNReal.ofReal ((1 - ε) ^ n) *
          volume (closedBall (0 : EuclideanSpace ℝ (Fin n)) (1 / 2)) := by
  sorry

end OMA.S_mo_29000

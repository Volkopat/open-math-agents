import Mathlib

/-!
# Meissner bodies and minimum volume (Wikipedia: 'In Meissner body')

Source: https://en.wikipedia.org/wiki/Meissner_body
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

Question (Bonnesen–Fenchel): are the two Meissner tetrahedra the minimum-volume three-dimensional
shapes of constant width?

Conventions:
* A body of constant width `1` is a nonempty compact convex `K ⊆ ℝ³` whose width
  `sup_{x ∈ K} ⟪u, x⟫ - inf_{x ∈ K} ⟪u, x⟫` is `1` in every unit direction `u`.
* Both Meissner bodies of width `1` have volume `(2/3 - (√3/4) arccos(1/3)) π` (Kawohl–Weber,
  'Meissner's mysterious bodies'), so the question asks whether this is the least volume of a
  body of constant width `1`; widths other than `1` follow by scaling. `main` states the answer
  yes as this volume inequality, the expected answer.
-/

namespace OMA.S_wp_in_meissner_body

open MeasureTheory

/-- Three-dimensional Euclidean space. -/
abbrev E := EuclideanSpace ℝ (Fin 3)

/-- `K` is a body of constant width `1`. -/
def IsConstantWidthOne (K : Set E) : Prop :=
  K.Nonempty ∧ IsCompact K ∧ Convex ℝ K ∧
    ∀ u : E, ‖u‖ = 1 →
      sSup ((fun x => inner ℝ u x) '' K) - sInf ((fun x => inner ℝ u x) '' K) = 1

/-- The volume of a Meissner body of width `1`. -/
noncomputable def meissnerVolume : ℝ :=
  (2 / 3 - Real.sqrt 3 / 4 * Real.arccos (1 / 3)) * Real.pi

/-- Every body of constant width `1` has volume at least that of a Meissner body. -/
theorem main : ∀ K : Set E, IsConstantWidthOne K → meissnerVolume ≤ (volume K).toReal := by
  sorry

end OMA.S_wp_in_meissner_body

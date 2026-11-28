import Mathlib

/-!
# Furstenberg's ×2 ×3 conjecture

Source: https://en.wikipedia.org/wiki/Hillel_Furstenberg
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

Conjecture (Furstenberg): every probability measure on the circle `ℝ/ℤ` that is invariant and
ergodic for the joint action of `x ↦ 2x` and `x ↦ 3x` is either Lebesgue measure or atomic.

Conventions.
* Circle: `AddCircle (1 : ℝ)` with its Haar probability measure `volume` (Lebesgue).
* Invariant: `μ` is preserved by both maps. Ergodic for the joint action: every measurable set
  `A` with `T₂⁻¹ A = A` and `T₃⁻¹ A = A` has `μ A = 0` or `μ Aᶜ = 0`.
* Atomic: `μ` is concentrated on a countable set (purely atomic). For an ergodic invariant
  measure this is the same as being supported on one finite periodic orbit.
-/

namespace OMA.S_wp_furstenberg

open MeasureTheory

/-- The circle `ℝ/ℤ`. -/
abbrev Circle1 := AddCircle (1 : ℝ)

/-- Multiplication by `k` on the circle. -/
def mulBy (k : ℕ) (x : Circle1) : Circle1 := k • x

/-- Furstenberg's conjecture. -/
theorem main :
    ∀ μ : Measure Circle1, IsProbabilityMeasure μ →
      MeasurePreserving (mulBy 2) μ μ → MeasurePreserving (mulBy 3) μ μ →
      (∀ A : Set Circle1, MeasurableSet A → mulBy 2 ⁻¹' A = A → mulBy 3 ⁻¹' A = A →
        μ A = 0 ∨ μ Aᶜ = 0) →
      μ = volume ∨ ∃ S : Set Circle1, S.Countable ∧ μ Sᶜ = 0 := by
  sorry

end OMA.S_wp_furstenberg

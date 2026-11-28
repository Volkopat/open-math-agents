import Mathlib

/-!
# Continuous doubling weight vanishing on a set of positive Lebesgue measure

Source: https://mathoverflow.net/questions/252839
Credit: @artnoage

The source asks for a continuous nonnegative weight on ℝ whose weighted Lebesgue
measure is a nonzero locally finite doubling Borel measure and whose zero set has
positive Lebesgue measure. Continuity implies local integrability. The doubling
test uses closed bounded intervals of positive radius. Endpoints have measure zero
because the weighted measure is absolutely continuous with respect to volume.
-/

namespace OMA.S_mo_252839

open MeasureTheory Set
open scoped ENNReal NNReal

/-- Lebesgue measure with density w. -/
noncomputable def weightedVolume (w : ℝ → ℝ≥0) : Measure ℝ :=
  volume.withDensity (fun x ↦ (w x : ℝ≥0∞))

/-- A nonzero locally finite measure that doubles on all centered intervals. -/
def IsDoubling (μ : Measure ℝ) : Prop :=
  μ ≠ 0 ∧ IsLocallyFiniteMeasure μ ∧
    ∃ C : ℝ≥0, ∀ x r : ℝ, 0 < r →
      μ (Icc (x - 2 * r) (x + 2 * r)) ≤ (C : ℝ≥0∞) * μ (Icc (x - r) (x + r))

theorem main :
    ∃ w : ℝ → ℝ≥0, Continuous w ∧ IsDoubling (weightedVolume w) ∧
      0 < volume {x : ℝ | w x = 0} := by
  sorry

end OMA.S_mo_252839

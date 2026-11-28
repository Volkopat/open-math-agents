import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# An inequality regarding centered Bernoulli random variables

Source: https://mathoverflow.net/questions/335144
Question by Student, 2019-06-30 (CC BY-SA 4.0).
Credit: @etaubman

The coefficient may depend on the number of random variables, but is uniform
across admissible joint distributions. Dependence is allowed. Measurability,
almost-sure support on {0,1}, and the common probability of 1 express exactly
the identical Bernoulli marginal laws in the question.

James Martin's source comment 837278 already describes a class of counterexamples:
an almost surely positive even number of zero variables makes the raw product
zero while the centered product is positive. The accompanying disproof gives
an explicit three-outcome probability space from this class.
-/

open MeasureTheory
open scoped BigOperators

namespace OMA.S_mo_335144

/-- The proposed uniform bound, with arbitrary dependence allowed. -/
theorem main :
    ∀ n : ℕ, 0 < n → ∃ C : ℝ, 0 < C ∧
      ∀ (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (V : Fin n → Ω → ℝ) (p : ℝ),
        (∀ i, Measurable (V i)) →
        (∀ i, ∀ᵐ ω ∂μ, V i ω = 0 ∨ V i ω = 1) →
        (∀ i, μ {ω | V i ω = 1} = ENNReal.ofReal p) →
        0 ≤ p → p < 1 / 2 →
        (∫ ω, ∏ i, (V i ω - p) ∂μ) ≤ C * (∫ ω, ∏ i, V i ω ∂μ) := by
  sorry

end OMA.S_mo_335144

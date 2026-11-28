import Mathlib

/-!
# Uniformity in the Lebesgue differentiation theorem

Source: https://mathoverflow.net/questions/450451
Credit: @artnoage

The initial question asks if the convergence of the paired centered averages is uniform
over nonnegative measurable f and g with integral f at most 1 and g at most 1, for
each fixed finite Borel measure on the real line. The positive radius is allowed to
range below the uniform threshold. The edit's swapped pairing is a separate question.

The integrands are nonnegative, so the formulas use Lebesgue integrals in ℝ≥0∞.
The boundedness conditions make both paired integrals finite. If the centered
interval has zero measure, the average is set to zero by the ℝ≥0∞ convention.
-/

namespace OMA.S_mo_450451

open MeasureTheory Set
open scoped ENNReal NNReal

/-- The average of g over the closed interval of radius r centered at x. -/
noncomputable def centeredAverage (μ : Measure ℝ) (r : ℝ) (g : ℝ → ℝ≥0)
    (x : ℝ) : ℝ≥0∞ :=
  (∫⁻ y in Icc (x - r) (x + r), (g y : ℝ≥0∞) ∂μ) / μ (Icc (x - r) (x + r))

/-- Whether the initial paired limit is uniform over f and g. -/
theorem main :
    ∀ (μ : Measure ℝ), IsFiniteMeasure μ → ∀ ε : ℝ, 0 < ε →
      ∃ δ : ℝ, 0 < δ ∧ ∀ r : ℝ, 0 < r → r < δ →
        ∀ f g : ℝ → ℝ≥0, Measurable f → Measurable g →
          (∫⁻ x, (f x : ℝ≥0∞) ∂μ) ≤ 1 → (∀ x, g x ≤ 1) →
            |(∫⁻ x, (f x : ℝ≥0∞) * centeredAverage μ r g x ∂μ).toReal -
                (∫⁻ x, (f x : ℝ≥0∞) * (g x : ℝ≥0∞) ∂μ).toReal| < ε := by
  sorry

end OMA.S_mo_450451

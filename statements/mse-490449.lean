import Mathlib

/-!
# Characterization of strong convergence of finite measures

Source: https://math.stackexchange.com/questions/490449/what-are-some-characterizations-of-the-strong-and-total-variation-topologies-on
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
Drafted in an earlier generic agent run; audited against the source statement before submission.

Question: For a sequence of finite measures `μ_n` and a finite measure `μ_0` on a
measurable space `Ω`, is it true that `μ_n` converges strongly (setwise) to `μ_0`
if and only if `∫ f dμ_n → ∫ f dμ_0` for every bounded measurable function
`f : Ω → ℝ`?
-/

namespace OMA.S_mse_490449

theorem main :
    ∀ (Ω : Type) [MeasurableSpace Ω]
      (μ : ℕ → MeasureTheory.Measure Ω) (μ₀ : MeasureTheory.Measure Ω),
      (∀ n, MeasureTheory.IsFiniteMeasure (μ n)) →
      MeasureTheory.IsFiniteMeasure μ₀ →
      ((∀ A : Set Ω, MeasurableSet A →
          Filter.Tendsto (fun n => (μ n A).toReal) Filter.atTop (nhds (μ₀ A).toReal)) ↔
        (∀ f : Ω → ℝ, Measurable f → (∃ C : ℝ, ∀ x, |f x| ≤ C) →
          Filter.Tendsto (fun n => ∫ x, f x ∂(μ n)) Filter.atTop (nhds (∫ x, f x ∂μ₀)))) := by
  sorry

end OMA.S_mse_490449

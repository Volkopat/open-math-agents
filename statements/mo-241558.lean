import Mathlib

/-! Source: https://mathoverflow.net/questions/241558 -/

open Filter MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal Topology

namespace OMA.S_mo_241558

/-- The recurrence copies initial zeros and uses the first nonzero observation
to initialize the positive iterates. -/
structure FollowsLogRecurrence (x a : ℕ → ℝ) : Prop where
  input_nonneg : ∀ n, 0 ≤ x n
  iterate_nonneg : ∀ n, 0 ≤ a n
  first_eq : a 0 = x 0
  step : ∀ n : ℕ,
    if (∑ i ∈ Finset.range (n + 1), x i) = 0 then
      a (n + 1) = x (n + 1)
    else
      0 < a n ∧ 0 < a (n + 1) ∧
        x (n + 1) = a (n + 1) + (∑ i ∈ Finset.range (n + 1), a i) *
          Real.log (a (n + 1) / a n)

/-- Deterministic convergence for positive Cesàro means, and almost-sure
convergence for independent Poisson observations of a common rate. -/
theorem main :
    (∀ (x a : ℕ → ℝ) (rate : ℝ), 0 < rate → FollowsLogRecurrence x a →
      Tendsto (fun n : ℕ => (∑ i ∈ Finset.range (n + 1), x i) / (n + 1 : ℝ))
        atTop (𝓝 rate) → Tendsto a atTop (𝓝 rate)) ∧
    (∀ (Ω : Type*) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
      (rate : ℝ≥0) (X : ℕ → Ω → ℕ) (a : ℕ → Ω → ℝ),
      iIndepFun X μ →
      (∀ n, HasLaw (X n) (poissonMeasure rate) μ) →
      (∀ᵐ ω ∂μ, FollowsLogRecurrence (fun n => (X n ω : ℝ)) (fun n => a n ω)) →
      ∀ᵐ ω ∂μ, Tendsto (fun n => a n ω) atTop (𝓝 (rate : ℝ))) := by
  sorry

end OMA.S_mo_241558

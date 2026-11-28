import Mathlib

/-!
# Does Lebesgue's Differentiation Theorem Follow from Lebesgue's Density Theorem?

Source: https://math.stackexchange.com/questions/3543357/is-it-true-that-lebesgues-differentiation-theorem-follows-from-lebesgues-densi
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
Drafted in an earlier generic agent run; audited against the source statement before submission.

## Problem Statement
Let `(X, d)` be a separable complete metric space and `μ` a Borel probability
measure on `(X, d)`. Suppose Lebesgue's density theorem holds in `(X, d, μ)`:
for every Borel set `A ⊆ X`,
`lim_{r → 0⁺} μ(A ∩ B̄(x, r)) / μ(B̄(x, r)) = 1`
for `μ`-almost every `x ∈ A ∩ supp(μ)`, where
`supp(μ) = {x ∈ X | ∀ r > 0, μ(B̄(x, r)) > 0}`.

Does Lebesgue's differentiation theorem necessarily hold in `(X, d, μ)`, i.e.,
for every `f ∈ L¹(μ)`,
`lim_{r → 0⁺} (1 / μ(B̄(x, r))) ∫_{B̄(x, r)} f dμ = f(x)`
for `μ`-almost every `x ∈ supp(μ)`?

## Formalization Notes
We use `MetricSpace X`, `CompleteSpace X`, `TopologicalSpace.SeparableSpace X`,
`MeasurableSpace X`, `BorelSpace X`, and `MeasureTheory.IsProbabilityMeasure μ`.
The support is defined as `supp μ = {x | ∀ r > 0, 0 < μ (Metric.closedBall x r)}`.
Limits as `r → 0⁺` use `nhdsWithin 0 (Set.Ioi 0)`.
-/

namespace OMA.S_mse_3543357

def measureSupp {X : Type} [MetricSpace X] [MeasurableSpace X]
    (μ : MeasureTheory.Measure X) : Set X :=
  {x : X | ∀ r : ℝ, 0 < r → 0 < μ (Metric.closedBall x r)}

theorem main :
    ∀ (X : Type) [MetricSpace X] [CompleteSpace X]
      [TopologicalSpace.SeparableSpace X]
      [MeasurableSpace X] [BorelSpace X]
      (μ : MeasureTheory.Measure X) [MeasureTheory.IsProbabilityMeasure μ],
      (∀ A : Set X, MeasurableSet A →
        ∀ᵐ x ∂μ, x ∈ A ∩ measureSupp μ →
          Filter.Tendsto
            (fun r : ℝ =>
              (μ (A ∩ Metric.closedBall x r)).toReal /
                (μ (Metric.closedBall x r)).toReal)
            (nhdsWithin 0 (Set.Ioi 0)) (nhds 1)) →
      ∀ f : X → ℝ, MeasureTheory.Integrable f μ →
        ∀ᵐ x ∂μ, x ∈ measureSupp μ →
          Filter.Tendsto
            (fun r : ℝ =>
              ((μ (Metric.closedBall x r)).toReal)⁻¹ *
                ∫ y in Metric.closedBall x r, f y ∂μ)
            (nhdsWithin 0 (Set.Ioi 0)) (nhds (f x)) := by
  sorry

end OMA.S_mse_3543357

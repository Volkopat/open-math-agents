import Mathlib

/-!
# Federer's GMT 2.10.26: Hausdorff Measure Coarea Inequality Without Extra Hypotheses

Source: https://math.stackexchange.com/questions/870912/open-problems-in-federers-geometric-measure-theory
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
Draft from an earlier generic agent run; audited against the source and re-checked before submission.

## Problem Statement
In Federer's Geometric Measure Theory (Theorem 2.10.25 and Question 2.10.26),
if `f : X → Y` is a Lipschitz map between metric spaces, `A ⊆ X`, and
`0 ≤ k < ∞`, `0 ≤ m < ∞`, then
`∫*_Y H^k(A ∩ f⁻¹{y}) dH^m(y) ≤ (Lip f)^m * (α(k) α(m) / α(k + m)) * H^{k+m}(A)`,
provided either `{y ∈ Y | H^k(A ∩ f⁻¹{y}) > 0}` is a countable union of sets of
finite `H^m`-measure, or `Y` is boundedly compact.
Federer asks (2.10.26) whether the inequality still holds unconditionally
without those extra hypotheses.

## Formalization Notes
Mathlib's `MeasureTheory.Measure.hausdorffMeasure d` is the unnormalised `d`-dimensional Hausdorff
measure, whereas Federer's `H^d` is `α(d) 2^(-d)` times it, `α(s) = π^(s/2) / Γ(s/2 + 1)`. Rewriting
both sides in Mathlib's normalisation, the factor `α(k) α(m) / α(k + m)` cancels exactly, so the
inequality reads `∫* μ^k(A ∩ f⁻¹{y}) dμ^m(y) ≤ (Lip f)^m μ^(k+m)(A)`. We define the upper integral `upperIntegral μ g`
as the infimum of `∫⁻ y, h y ∂μ` over all measurable functions `h ≥ g`.
-/

namespace OMA.S_mse_870912

noncomputable def upperIntegral {Y : Type*} [MeasurableSpace Y]
    (μ : MeasureTheory.Measure Y) (g : Y → ENNReal) : ENNReal :=
  ⨅ (h : Y → ENNReal) (_ : Measurable h) (_ : g ≤ h), ∫⁻ y, h y ∂μ

theorem main :
    ∀ (X Y : Type) [MetricSpace X] [MetricSpace Y] [MeasurableSpace X] [BorelSpace X]
      [MeasurableSpace Y] [BorelSpace Y]
      (f : X → Y) (L : NNReal),
      LipschitzWith L f →
      ∀ (A : Set X) (k m : ℝ), 0 ≤ k → 0 ≤ m →
        upperIntegral (MeasureTheory.Measure.hausdorffMeasure m)
          (fun y => MeasureTheory.Measure.hausdorffMeasure k (A ∩ f ⁻¹' {y})) ≤
        ((L : ENNReal) ^ m) *
          MeasureTheory.Measure.hausdorffMeasure (k + m) A := by
  sorry

end OMA.S_mse_870912

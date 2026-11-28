import Mathlib

/-!
# The distance problem: every density whose support contains `0` is feasible

Source: https://arxiv.org/abs/2403.10926
Credit: @tox5tox5

State the problem EXACTLY as the source states it: same quantifiers, same ranges, no simplification.
Do not prove it here: the theorem body stays `sorry`. A person reviews the translation before merging.

D. J. Aldous, G. Blanc and N. Curien, "The distance problem on measured metric spaces"
(arXiv:2403.10926). Let `μ` be a Borel probability measure on a complete separable metric space
`(S, d)`, let `ξ₁, ξ₂` be independent with law `μ`, and let `D = d(ξ₁, ξ₂)`. A distribution on
`ℝ₊` is *feasible* if it arises as the law of `D` for some such `(S, d, μ)`. Open problem stated in
the paper: "Prove that for every probability density function `f` on `ℝ₊` whose support contains
`0`, the distribution with density `f` is feasible." (The paper proves that feasible laws have `0`
in their support, that finitely supported laws with an atom at `0` are feasible, and approximate
versions for densities positive near `0`.) This file states the open problem.

Modelling choices:
* `f : ℝ → ℝ≥0∞` is a measurable probability density vanishing on `(-∞, 0)`, and "the
  distribution with density `f`" is `volume.withDensity f` on `ℝ`.
* "The support contains `0`" (support of the distribution) means every neighbourhood of `0` has
  positive mass: `0 < ∫_{[0, ε)} f` for every `ε > 0`.
* The law of `D = d(ξ₁, ξ₂)` for independent `ξ₁, ξ₂ ∼ μ` is the push-forward of `μ ⊗ μ` under
  `(x, y) ↦ dist x y`. The space is a complete separable metric space with its Borel σ-algebra.
-/

namespace OMA.S_arxiv_2403_10926

open MeasureTheory

/-- **Aldous–Blanc–Curien, open problem.** -/
theorem main :
    ∀ f : ℝ → ENNReal, Measurable f → (∀ x < 0, f x = 0) → ∫⁻ x, f x = 1 →
      (∀ ε > 0, 0 < ∫⁻ x in Set.Ico (0 : ℝ) ε, f x) →
      ∃ (S : Type) (_ : MetricSpace S) (_ : CompleteSpace S)
        (_ : TopologicalSpace.SeparableSpace S) (_ : MeasurableSpace S) (_ : BorelSpace S)
        (μ : Measure S), IsProbabilityMeasure μ ∧
          (μ.prod μ).map (fun q : S × S => dist q.1 q.2) = volume.withDensity f := by
  sorry

end OMA.S_arxiv_2403_10926

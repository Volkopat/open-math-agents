import Mathlib

/-!
# An entropy bound in terms of the `L^p` distance of a density to `1`

Source: https://mathoverflow.net/questions/370909
Asked by MathOverflow user Daniel Li (An elementary inequality).

Let `μ` be a probability measure and `f` a probability density with respect to `μ`. For
`p > 1` the question asks for a proof of
`∫ f log f dμ ≤ 2 (∫ |f - 1|^p dμ)^{1/p} + 2/(p - 1) ∫ |f - 1|^p dμ`.

Translation choices.
* `μ` is a probability measure on a measurable space `Ω` (as clarified in the comments, `f`
  is a density with respect to the probability measure `μ`). A probability density is a
  measurable `f ≥ 0` with `∫ f dμ = 1`.
* We assume that `|f - 1|^p` is integrable, i.e. that the right-hand side is finite;
  otherwise the inequality is trivial (its right-hand side is `+∞`), but Lean's Bochner
  integral would assign the value `0` to the non-integrable integral.
* `∫ f log f dμ` is the Bochner integral of `f * Real.log f` (with `0 log 0 = 0`).
-/

namespace OMA.S_mo_370909

open MeasureTheory

theorem main :
    ∀ (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] (f : Ω → ℝ)
      (p : ℝ), 1 < p → Measurable f → (∀ x, 0 ≤ f x) → ∫ x, f x ∂μ = 1 →
      Integrable (fun x => |f x - 1| ^ p) μ →
      ∫ x, f x * Real.log (f x) ∂μ ≤
        2 * (∫ x, |f x - 1| ^ p ∂μ) ^ (1 / p) + 2 / (p - 1) * ∫ x, |f x - 1| ^ p ∂μ := by
  sorry

end OMA.S_mo_370909

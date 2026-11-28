import Mathlib

/-!
# The Gaussian completely monotone conjecture (entropy along the heat flow)

Source: https://mathoverflow.net/questions/501605
Credit: @tox5tox5

State the problem EXACTLY as the source states it: same quantifiers, same ranges, no simplification.
Do not prove it here: the theorem body stays `sorry`. A person reviews the translation before merging.

The question (MathOverflow 501605, Oct 2025): let `X` be a random vector in `ℝᵈ` and
`X_t = X + √t Z`, `t > 0`, with `Z` an independent standard normal vector, and let `f_t` be the
density of `X_t`. Is it true that the derivatives in `t` of the entropy `∫ f_t ln f_t dx` have
alternating signs? A comment identifies this as the "Gaussian completely monotone" conjecture, and
the answer quotes its form from the literature: for all `t > 0`, `(-1)^m (dᵐ/dtᵐ) H(μ_t) ≥ 0`,
where `H(μ) = ∫ dμ log (dμ/dx)` is the (negative) differential entropy (stated there for
`X_0 + √(2t) G`; the time change `t ↦ 2t` does not affect the signs). It is known for `m ≤ 2` in all
dimensions, and for more derivatives in low dimension or under log-concavity; the general case is
open. This file states the conjecture in the question's parametrization.

Modelling choices:
* `X` is given by its law `μ`, a probability measure on `EuclideanSpace ℝ (Fin d)`, `d ≥ 1`; the
  density of `X_t` is the Gaussian convolution
  `f_t(x) = ∫ (2πt)^{-d/2} exp(-‖x - y‖² / (2t)) dμ(y)`.
* For `∫ f_t ln f_t` to be a well-defined real number for all `t > 0`, `X` is assumed to have a
  finite second moment (an added regularity hypothesis, made explicit here).
* The claim is `(-1)^m (dᵐ/dtᵐ) ∫ f_t ln f_t ≥ 0` for every `m ≥ 1` and `t > 0`, with
  `iteratedDeriv`.
-/

namespace OMA.S_mo_501605

open MeasureTheory

/-- The density at `x` of `X + √t Z`, where `X` has law `μ` and `Z` is standard normal on `ℝᵈ`. -/
noncomputable def density (d : ℕ) (μ : Measure (EuclideanSpace ℝ (Fin d))) (t : ℝ)
    (x : EuclideanSpace ℝ (Fin d)) : ℝ :=
  ∫ y, (2 * Real.pi * t) ^ (-(d : ℝ) / 2) * Real.exp (-‖x - y‖ ^ 2 / (2 * t)) ∂μ

/-- The negative entropy `H(X_t) = ∫ f_t ln f_t`. -/
noncomputable def negEntropy (d : ℕ) (μ : Measure (EuclideanSpace ℝ (Fin d))) (t : ℝ) : ℝ :=
  ∫ x, density d μ t x * Real.log (density d μ t x)

/-- **Gaussian completely monotone conjecture (MathOverflow 501605).** -/
theorem main :
    ∀ (d : ℕ) (μ : Measure (EuclideanSpace ℝ (Fin d))), 1 ≤ d → IsProbabilityMeasure μ →
      Integrable (fun y => ‖y‖ ^ 2) μ →
      ∀ m : ℕ, 1 ≤ m → ∀ t : ℝ, 0 < t →
        0 ≤ (-1) ^ m * iteratedDeriv m (negEntropy d μ) t := by
  sorry

end OMA.S_mo_501605

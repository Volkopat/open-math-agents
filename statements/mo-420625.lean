import Mathlib

/-!
# Are the derivatives of the entropy power along the heat flow alternating in sign?

Source: https://mathoverflow.net/questions/420625
Credit: @tox5tox5

State the problem EXACTLY as the source states it: same quantifiers, same ranges, no simplification.
Do not prove it here: the theorem body stays `sorry`. A person reviews the translation before merging.

The question (MathOverflow 420625, Alex Savignon, Apr 2022): let `X` be a random vector in `ℝᵈ`
and `X_t = X + √t N`, `t > 0`, with `N` an independent standard normal vector; let
`H(X_t) = -∫ f_t ln f_t dx` with `f_t` the density of `X_t`, and `N(t) = e^{(2/d) H(X_t)}` the
entropy power. Known: `N' ≥ 0`, `N'' ≤ 0` (Costa), and `N''' ≥ 0` for log-concave `X` (Toscani).
"Could it be that the signs of the successive derivatives of `N` are alternating?" Asked in a
comment whether this means `(-1)^{k-1} N^{(k)} > 0` for all `k`, the asker replied "this should
hold for any `X`". Answers point to Ledoux's "completely monotone conjecture"; it is open. This
file states the alternating-sign property, with non-strict signs as in the known cases quoted
in the question (for Gaussian `X` the entropy power is linear in `t`, so higher derivatives vanish).

Modelling choices:
* `X` is given by its law `μ`, a probability measure on `EuclideanSpace ℝ (Fin d)`, `d ≥ 1`. The
  density of `X_t = X + √t N` is written explicitly as the Gaussian convolution
  `f_t(x) = ∫ (2πt)^{-d/2} exp(-‖x - y‖² / (2t)) dμ(y)`.
* For `H(X_t)` to be a well-defined real number for all `t > 0`, `X` is assumed to have a finite
  second moment (the standard setting of Costa's entropy power inequality); this is an added
  regularity hypothesis, made explicit here because the source says "any `X`".
* `N^{(k)}(t)` is `iteratedDeriv k N t`; the claim is `(-1)^{k-1} N^{(k)}(t) ≥ 0` for every `k ≥ 1`
  and every `t > 0`.
-/

namespace OMA.S_mo_420625

open MeasureTheory

/-- The density at `x` of `X + √t N`, where `X` has law `μ` and `N` is standard normal on `ℝᵈ`. -/
noncomputable def density (d : ℕ) (μ : Measure (EuclideanSpace ℝ (Fin d))) (t : ℝ)
    (x : EuclideanSpace ℝ (Fin d)) : ℝ :=
  ∫ y, (2 * Real.pi * t) ^ (-(d : ℝ) / 2) * Real.exp (-‖x - y‖ ^ 2 / (2 * t)) ∂μ

/-- The differential entropy `H(X_t) = -∫ f_t ln f_t`. -/
noncomputable def entropy (d : ℕ) (μ : Measure (EuclideanSpace ℝ (Fin d))) (t : ℝ) : ℝ :=
  -∫ x, density d μ t x * Real.log (density d μ t x)

/-- The entropy power `N(t) = e^{(2/d) H(X_t)}`. -/
noncomputable def entropyPower (d : ℕ) (μ : Measure (EuclideanSpace ℝ (Fin d))) (t : ℝ) : ℝ :=
  Real.exp (2 / d * entropy d μ t)

/-- **MathOverflow 420625 (completely monotone conjecture for the entropy power).** -/
theorem main :
    ∀ (d : ℕ) (μ : Measure (EuclideanSpace ℝ (Fin d))), 1 ≤ d → IsProbabilityMeasure μ →
      Integrable (fun y => ‖y‖ ^ 2) μ →
      ∀ k : ℕ, 1 ≤ k → ∀ t : ℝ, 0 < t →
        0 ≤ (-1) ^ (k - 1) * iteratedDeriv k (entropyPower d μ) t := by
  sorry

end OMA.S_mo_420625

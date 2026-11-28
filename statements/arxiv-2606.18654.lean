import Mathlib

/-!
# Two-point rigidity of infinite exchangeable sequences with Gaussian pairs

Source: https://arxiv.org/abs/2606.18654
Credit: @tox5tox5

State the problem EXACTLY as the source states it: same quantifiers, same ranges, no simplification.
Do not prove it here: the theorem body stays `sorry`. A person reviews the translation before merging.

M. Newman, "Rigidity of infinite exchangeable sequences with Gaussian marginals"
(arXiv:2606.18654), Conjecture 1.2: let `X = (X_i)_{i=1}^∞` be an infinite exchangeable sequence of
random variables. If `(X₁, X₂)` is a centered multivariate Gaussian, then `X` is a Gaussian process.
(The paper proves this when `(X₁, X₂, X₃, X₄)` is assumed Gaussian, and when the directing measure
is infinitely divisible; finite exchangeable sequences give counterexamples.) This file states
Conjecture 1.2.

Modelling choices:
* The sequence is `X i`, `i : ℕ` (so `X 0, X 1` play the role of `X₁, X₂`), real-valued and
  measurable on a probability space.
* Exchangeable: for every `n` and every permutation `σ` of `Fin n`, the vectors
  `(X_{σ 0}, …, X_{σ (n-1)})` and `(X_0, …, X_{n-1})` have the same law.
* "`(X₁, X₂)` is a centered multivariate Gaussian": the law of `(X 0, X 1)` on `ℝ × ℝ` is Gaussian
  (`IsGaussian`: every continuous linear functional has a real Gaussian law) and `X 0`, `X 1` have
  mean `0`.
* "`X` is a Gaussian process": for every `n`, the law of `(X_0, …, X_{n-1})` on `Fin n → ℝ` is
  Gaussian.
-/

namespace OMA.S_arxiv_2606_18654

open MeasureTheory ProbabilityTheory

/-- **Newman, Conjecture 1.2.** -/
theorem main :
    ∀ (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] (X : ℕ → Ω → ℝ),
      (∀ i, Measurable (X i)) →
      -- exchangeability
      (∀ (n : ℕ) (σ : Equiv.Perm (Fin n)),
        μ.map (fun ω (i : Fin n) => X (σ i) ω) = μ.map (fun ω (i : Fin n) => X i ω)) →
      -- `(X₁, X₂)` is a centered Gaussian vector
      IsGaussian (μ.map fun ω => (X 0 ω, X 1 ω)) →
      ∫ ω, X 0 ω ∂μ = 0 → ∫ ω, X 1 ω ∂μ = 0 →
      -- then every finite-dimensional marginal is Gaussian
      ∀ n : ℕ, IsGaussian (μ.map fun ω (i : Fin n) => X i ω) := by
  sorry

end OMA.S_arxiv_2606_18654

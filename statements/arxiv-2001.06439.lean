import Mathlib

/-!
# Log-convexity of moments of averages of i.i.d. nonnegative random variables (order `p > 1`)

Source: https://arxiv.org/abs/2001.06439
Credit: @tox5tox5

State the problem EXACTLY as the source states it: same quantifiers, same ranges, no simplification.
Do not prove it here: the theorem body stays `sorry`. A person reviews the translation before merging.

P. Lamkin and T. Tkocz, "Log-concavity and log-convexity of moments of averages of i.i.d. random
variables" (arXiv:2001.06439, Canad. Math. Bull. 2022). For i.i.d. `X₁, X₂, …` let
`b_n = E((X₁ + ⋯ + X_n)/n)^p`, `n = 1, 2, …`; a nonnegative sequence is log-convex if
`b_n² ≤ b_{n-1} b_{n+1}` for all `n ≥ 2`. Conjecture 1: let `p > 1` and let `X₁, X₂, …` be i.i.d.
nonnegative random variables; then `(b_n)` is log-convex. (The paper proves it for `n ≥ p²` when
`p` is an integer, and for `p = 2, 3`; it proves the cases `p < 0` and `0 < p < 1`.) This file
states Conjecture 1.

Modelling choices:
* The variables are `X i`, `i : ℕ` (`X 0` is `X₁`), measurable, mutually independent (`iIndepFun`),
  identically distributed and nonnegative on a probability space.
* `b n` is the lower Lebesgue integral of `((X₀ + ⋯ + X_{n-1}) / n)^p` (real power, cast to
  `ℝ≥0∞`), so it is defined even when infinite. If `E X^p = ∞` then every `b_n = ∞` (since
  `b_n ≥ n^{-p} E X₁^p`) and the inequality is trivial, so no integrability hypothesis is needed.
-/

namespace OMA.S_arxiv_2001_06439

open MeasureTheory ProbabilityTheory

/-- `b_n = E((X₁ + ⋯ + X_n)/n)^p`, in `[0, ∞]`. -/
noncomputable def b {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) (X : ℕ → Ω → ℝ) (p : ℝ)
    (n : ℕ) : ENNReal :=
  ∫⁻ ω, ENNReal.ofReal (((∑ i ∈ Finset.range n, X i ω) / n) ^ p) ∂μ

/-- **Lamkin–Tkocz, Conjecture 1.** -/
theorem main :
    ∀ (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
      (X : ℕ → Ω → ℝ) (p : ℝ), 1 < p →
      (∀ i, Measurable (X i)) → iIndepFun X μ → (∀ i, μ.map (X i) = μ.map (X 0)) →
      (∀ i ω, 0 ≤ X i ω) →
      ∀ n : ℕ, 2 ≤ n → b μ X p n ^ 2 ≤ b μ X p (n - 1) * b μ X p (n + 1) := by
  sorry

end OMA.S_arxiv_2001_06439

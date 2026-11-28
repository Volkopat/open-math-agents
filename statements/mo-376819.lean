import Mathlib

/-!
# The minimum of the running means of i.i.d. exponential variables is uniform on (0, 1)

Source: https://mathoverflow.net/questions/376819
Credit: @tox5tox5

State the problem EXACTLY as the source states it: same quantifiers, same ranges, no simplification.
Do not prove it here: the theorem body stays `sorry`. A person reviews the translation before merging.

The question (MathOverflow 376819, John Wong, Nov 2020): let `X₁, …, Xₙ, …` be i.i.d. exponential
random variables with mean `1`. "It is well-known that `min_{1 ≤ j < ∞} (X₁ + ⋯ + X_j) / j`
follows the uniform distribution `U(0,1)`"; the asker wants a reference. Answers on the page
(Iosif Pinelis and others) prove the statement. This file states it.

Modelling choices:
* The variables are `X i`, `i : ℕ` (so `X 0` is `X₁`), measurable, mutually independent
  (`iIndepFun`), each with law `expMeasure 1` (Mathlib's exponential distribution with rate `1`,
  i.e. mean `1`), on an arbitrary probability space.
* The minimum over `j ≥ 1` is written as the infimum `⨅ j : ℕ, (X 0 + ⋯ + X j) / (j + 1)`. The
  answers note the minimum is attained almost surely, so this is the same random variable a.s.
* "Follows `U(0,1)`" is stated as: its law is Lebesgue measure restricted to `[0, 1]`.
-/

namespace OMA.S_mo_376819

open MeasureTheory ProbabilityTheory

/-- **MathOverflow 376819.** For i.i.d. mean-one exponential variables, the minimum of the
running means is uniformly distributed on `[0, 1]`. -/
theorem main :
    ∀ (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
      (X : ℕ → Ω → ℝ),
      (∀ i, Measurable (X i)) →
      iIndepFun X μ →
      (∀ i, μ.map (X i) = expMeasure 1) →
      μ.map (fun ω => ⨅ j : ℕ, (∑ i ∈ Finset.range (j + 1), X i ω) / ((j : ℝ) + 1)) =
        volume.restrict (Set.Icc (0 : ℝ) 1) := by
  sorry

end OMA.S_mo_376819

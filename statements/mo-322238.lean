import Mathlib

/-!
# Is a weighted sum of independent noncentral chi-squared variables log-concave?

Source: https://mathoverflow.net/questions/322238
Credit: @tox5tox5

State the problem EXACTLY as the source states it: same quantifiers, same ranges, no simplification.
Do not prove it here: the theorem body stays `sorry`. A person reviews the translation before merging.

The question (MathOverflow 322238, Clement C., Feb 2019): let `n ≥ 2` and `X₁, …, Xₙ` be
independent noncentral chi-squared random variables, `Xᵢ ∼ χ²(δᵢ)`, and `w₁, …, wₙ > 0`. With
`X = ∑ wᵢ Xᵢ`, is it true that the distribution of `X` is log-concave (its pdf is a log-concave
function)? (The asker notes it holds when all weights are equal, and asks about the central case.)
A comment (2025) reports that for `n = 2`, `δᵢ = 0` (central) and unequal weights, the density is
actually log-convex, by explicit computation. So the answer to the general question is negative,
and this file states that negative answer.

Modelling choices:
* `χ²(δ)` is the noncentral chi-squared law with one degree of freedom and noncentrality `δ ≥ 0`,
  i.e. the law of `Z²` with `Z ∼ N(√δ, 1)`. (One degree of freedom matches the asker's remark: with
  equal weights the sum is a chi-squared law with `n ≥ 2` degrees of freedom, which is
  log-concave.)
* The variables are measurable and mutually independent (`iIndepFun`) on a probability space.
* "The distribution of `X` is log-concave" means it has a Lebesgue density `f ≥ 0` (some version)
  with `f(θx + (1-θ)y) ≥ f(x)^θ f(y)^(1-θ)` for all `x, y` and `θ ∈ [0, 1]`.
* `main` is the negation of the claim "for all `n ≥ 2`, `δ`, `w` the distribution is
  log-concave".
-/

namespace OMA.S_mo_322238

open MeasureTheory ProbabilityTheory

/-- The noncentral chi-squared law `χ²(δ)` with one degree of freedom: the law of `Z²`,
`Z ∼ N(√δ, 1)`. -/
noncomputable def chiSq (δ : ℝ) : Measure ℝ :=
  (gaussianReal (Real.sqrt δ) 1).map fun z => z ^ 2

/-- A measure on `ℝ` has a log-concave density with respect to Lebesgue measure. -/
def HasLogConcaveDensity (ν : Measure ℝ) : Prop :=
  ∃ f : ℝ → ℝ, (∀ x, 0 ≤ f x) ∧ ν = volume.withDensity (fun x => ENNReal.ofReal (f x)) ∧
    ∀ x y θ : ℝ, 0 ≤ θ → θ ≤ 1 → f x ^ θ * f y ^ (1 - θ) ≤ f (θ * x + (1 - θ) * y)

/-- **MathOverflow 322238 (negative answer).** It is not true that every positive weighted sum of
`n ≥ 2` independent noncentral chi-squared variables has a log-concave distribution. -/
theorem main :
    ¬ ∀ (n : ℕ) (δ w : Fin n → ℝ), 2 ≤ n → (∀ i, 0 ≤ δ i) → (∀ i, 0 < w i) →
        ∀ (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
          (X : Fin n → Ω → ℝ),
          (∀ i, Measurable (X i)) → iIndepFun X μ → (∀ i, μ.map (X i) = chiSq (δ i)) →
            HasLogConcaveDensity (μ.map fun ω => ∑ i, w i * X i ω) := by
  sorry

end OMA.S_mo_322238

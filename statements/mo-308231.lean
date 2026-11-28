import Mathlib

/-!
# Is the maximum of independent Poisson random variables log-concave?

Source: https://mathoverflow.net/questions/308231
Credit: @tox5tox5

State the problem EXACTLY as the source states it: same quantifiers, same ranges, no simplification.
Do not prove it here: the theorem body stays `sorry`. A person reviews the translation before merging.

The question (MathOverflow 308231, asked by TOM, Aug 2018): let `X₁, …, Xₙ` be independent Poisson
random variables with parameter `λ > 0`, let `Mₙ = max {X₁, …, Xₙ}` and `p_j = P(Mₙ = j)`.
Is `Mₙ` log-concave, i.e. is `p_j² ≥ p_{j-1} p_{j+1}`?

An answer (2026) states that the answer is affirmative, citing Theorem 2 of "Ultra log-concavity
of discrete order statistics" (discrete order statistics of i.i.d. ultra log-concave variables are
ultra log-concave, and the Poisson law is ultra log-concave). This file states the affirmative
answer.

Modelling choices:
* The variables live on an arbitrary probability space `(Ω, μ)`, are measurable, mutually
  independent (`iIndepFun`), and each has law `poissonMeasure λ` (Mathlib's Poisson distribution
  with rate `λ`). The rate is taken in `ℝ≥0` with `0 < λ`, as in the source.
* `n ≥ 1`, so that the maximum is over a nonempty family; it is `Finset.univ.sup` over `Fin n`
  with values in `ℕ`.
* `p j = μ.real {Mₙ = j}`. The source's inequality `p_j² ≥ p_{j-1} p_{j+1}` concerns indices
  `j ≥ 1` (for `j = 0`, `p_{-1} = 0` and it is trivial); it is written as
  `p j * p (j + 2) ≤ p (j + 1) ^ 2` for all `j : ℕ`. No extra "no internal zeros" condition is
  imposed, matching the source's definition of log-concavity.
-/

namespace OMA.S_mo_308231

open MeasureTheory ProbabilityTheory
open scoped NNReal

/-- **MathOverflow 308231.** The maximum of `n` independent Poisson(`λ`) random variables has a
log-concave probability mass function. -/
theorem main :
    ∀ (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
      (lam : ℝ≥0) (n : ℕ) (X : Fin n → Ω → ℕ),
      0 < lam → 1 ≤ n →
      (∀ i, Measurable (X i)) →
      iIndepFun X μ →
      (∀ i, μ.map (X i) = poissonMeasure lam) →
      ∀ j : ℕ,
        μ.real {ω | Finset.univ.sup (fun i => X i ω) = j} *
            μ.real {ω | Finset.univ.sup (fun i => X i ω) = j + 2} ≤
          μ.real {ω | Finset.univ.sup (fun i => X i ω) = j + 1} ^ 2 := by
  sorry

end OMA.S_mo_308231

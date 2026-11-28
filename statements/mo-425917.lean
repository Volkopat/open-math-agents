import Mathlib

/-!
# Is the Beta distribution decomposable for `α, β ≥ 1`?

Source: https://mathoverflow.net/questions/425917
Credit: @tox5tox5

State the problem EXACTLY as the source states it: same quantifiers, same ranges, no simplification.
Do not prove it here: the theorem body stays `sorry`. A person reviews the translation before merging.

The question (MathOverflow 425917, Daniel Turizo, Jul 2022): let `Y ∼ Beta(α, β)`. Is it possible
to decompose `Y = X₁ + X₂` with non-constant, independent random variables `X₁, X₂`? The asker
cites Linnik–Ostrovskii for a negative answer when `α + β < 1` and asks about `α, β ≥ 1`. A comment
shows the answer is positive for `α = β = 1` (`X₁ ∼ U(0, 1/2)`, `X₂` uniform on `{0, 1/2}`). The
page has no answer for general `α, β ≥ 1`; `main` states the affirmative answer for that range.

Modelling choices:
* `Beta(α, β)` is Mathlib's `betaMeasure α β`.
* "`Y = X₁ + X₂` with `X₁, X₂` independent" is stated for laws: the law of `Y` is the additive
  convolution `ν₁ ∗ ν₂` of the laws of `X₁` and `X₂` (any such pair of laws is realized by
  independent variables on a product space, and conversely).
* "Non-constant" means the law is a probability measure that is not a Dirac mass.
-/

namespace OMA.S_mo_425917

open MeasureTheory ProbabilityTheory

/-- **MathOverflow 425917 (affirmative answer for `α, β ≥ 1`).** For all `α, β ≥ 1`, the
`Beta(α, β)` law is the convolution of two non-degenerate probability laws. -/
theorem main :
    ∀ α β : ℝ, 1 ≤ α → 1 ≤ β →
      ∃ ν₁ ν₂ : Measure ℝ, IsProbabilityMeasure ν₁ ∧ IsProbabilityMeasure ν₂ ∧
        (∀ c : ℝ, ν₁ ≠ Measure.dirac c) ∧ (∀ c : ℝ, ν₂ ≠ Measure.dirac c) ∧
        ν₁.conv ν₂ = betaMeasure α β := by
  sorry

end OMA.S_mo_425917

import Mathlib

/-!
# Can `E|X - X'| ≥ E|X - m|` be improved by a constant factor?

Source: https://mathoverflow.net/questions/195973
Credit: @koolkao

Question (billo, MathOverflow 195973, 2015; CC BY-SA 3.0). Suppose that `X` is a random variable
with finite first moment and median `m`. Let `X'` be an independent copy of `X`. What
inequalities relate `E|X - X'|` and `E|X - m|`? What is the best lower bound on `E|X - X'|` in
terms of `E|X - m|`? We easily see that `E|X - X'| ≥ E|X - m|`. Can this inequality be improved
to `E|X - X'| ≥ c E|X - m|` for some `c > 1`? If not, what additional assumptions are needed for
this to hold?

`main` states that the inequality can be improved: there is `c > 1` with
`c E|X - m| ≤ E|X - X'|` for every such `X` and every median `m` of `X`. A disproof shows that for
every `c > 1` some distribution and median violate this. The other questions in the post are not
stated.

Translation choices:
* the law of `X` is a probability measure `μ` on `ℝ` with `Integrable id μ` (finite first
  moment);
* `m` is a median of `μ` if `μ (Iic m) ≥ 1/2` and `μ (Ici m) ≥ 1/2` (medians need not be
  unique; the inequality is asked for every median);
* `E|X - m| = ∫ x, |x - m| ∂μ` and, since `X'` is an independent copy of `X`,
  `E|X - X'| = ∫ x, ∫ y, |x - y| ∂μ ∂μ`.
-/

namespace OMA.S_mo_195973

open MeasureTheory

/-- There is `c > 1` with `c E|X - m| ≤ E|X - X'|` for every integrable `X` and median `m`. -/
theorem main :
    ∃ c : ℝ, 1 < c ∧ ∀ μ : Measure ℝ, IsProbabilityMeasure μ → Integrable id μ →
      ∀ m : ℝ, 2⁻¹ ≤ μ (Set.Iic m) → 2⁻¹ ≤ μ (Set.Ici m) →
        c * ∫ x, |x - m| ∂μ ≤ ∫ x, ∫ y, |x - y| ∂μ ∂μ := by
  sorry

end OMA.S_mo_195973

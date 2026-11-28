import Mathlib

/-!
# `∫_{-c}^{c} |A ∩ (x + A)| dx` is maximized by a centered interval

Source: https://mathoverflow.net/questions/415722
Credit: @tox5tox5

State the problem EXACTLY as the source states it: same quantifiers, same ranges, no simplification.
Do not prove it here: the theorem body stays `sorry`. A person reviews the translation before merging.

The question (MathOverflow 415722, Feb 2022): let `A ⊆ ℝ` be a nonempty measurable set with Lebesgue
measure `|A| = 1`, let `c > 0`, and define `I(A) := ∫_{-c}^{c} |A ∩ (x + A)| dx`. Under the
constraint `|A| = 1`, is `I(A)` maximized when `A` is an interval centered at the origin, i.e.
`[-1/2, 1/2]`? Terry Tao answers in a comment that this is immediate from the Riesz rearrangement
inequality, since `I(A) = ∫∫ 1_A(x) 1_A(x - y) 1_{[-c,c]}(y) dx dy`, and the accepted answer records
this affirmative answer. This file states it.

Modelling choices:
* `|·|` is Lebesgue measure `volume` on `ℝ` (with values in `ℝ≥0∞`), `x + A` is the translate
  `{y | y - x ∈ A}`, and `I(A)` is the lower Lebesgue integral over `[-c, c]`.
* "Maximized at `[-1/2, 1/2]`" is stated as `I(A) ≤ I([-1/2, 1/2])` for every measurable `A` with
  `|A| = 1` (such an `A` is automatically nonempty).
-/

namespace OMA.S_mo_415722

open MeasureTheory

/-- `I(A) = ∫_{-c}^{c} |A ∩ (x + A)| dx`. -/
noncomputable def I (c : ℝ) (A : Set ℝ) : ENNReal :=
  ∫⁻ x in Set.Icc (-c) c, volume (A ∩ {y | y - x ∈ A})

/-- **MathOverflow 415722 (affirmative answer).** -/
theorem main :
    ∀ (c : ℝ), 0 < c → ∀ A : Set ℝ, MeasurableSet A → volume A = 1 →
      I c A ≤ I c (Set.Icc (-1 / 2) (1 / 2)) := by
  sorry

end OMA.S_mo_415722

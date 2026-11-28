import Mathlib

/-!
# Are the convolution roots of an infinitely divisible probability infinitely divisible?

Source: https://mathoverflow.net/questions/294245
Credit: @tox5tox5

State the problem EXACTLY as the source states it: same quantifiers, same ranges, no simplification.
Do not prove it here: the theorem body stays `sorry`. A person reviews the translation before merging.

The question (MathOverflow 294245, Alex M., Mar 2018): let `μ` be an infinitely divisible
probability on a topological group `G`. If `ν^{∗n} = μ` for some `n`, is `ν` an infinitely
divisible probability too? A comment answers in the negative: in `ℤ/3ℤ`, `δ₀ = δ₂^{∗3}`, and `δ₀`
is infinitely divisible while `δ₂` is not. (The follow-up parts of the question ask for classes of
groups where the answer is affirmative; they are not formalized here.) This file states the
negative answer to the main question.

Modelling choices:
* `G` is a topological group with its Borel σ-algebra; measures are Borel measures and the
  convolution is Mathlib's `Measure.mconv` (`(μ ∗ₘ ν)` is the push-forward of `μ ⊗ ν` under
  multiplication). `ν^{∗n}` is the `n`-fold convolution power, with `ν^{∗0} = δ₁`.
* `μ` is infinitely divisible if for every `k ≥ 1` there is a probability measure `ρ` with
  `ρ^{∗k} = μ`.
* "For some `n`" is read as `n ≥ 1` (for `n = 0` the hypothesis says nothing about `ν`).
-/

namespace OMA.S_mo_294245

open MeasureTheory

/-- The `n`-fold convolution power of a measure on a monoid (`ν^{∗0} = δ₁`). -/
noncomputable def convPow {G : Type} [Monoid G] [MeasurableSpace G] (ν : Measure G) :
    ℕ → Measure G
  | 0 => Measure.dirac 1
  | n + 1 => ν.mconv (convPow ν n)

/-- A probability measure is infinitely divisible if it has a probability `k`-th convolution root
for every `k ≥ 1`. -/
def IsInfDiv {G : Type} [Monoid G] [MeasurableSpace G] (μ : Measure G) : Prop :=
  IsProbabilityMeasure μ ∧
    ∀ k : ℕ, 1 ≤ k → ∃ ρ : Measure G, IsProbabilityMeasure ρ ∧ convPow ρ k = μ

/-- **MathOverflow 294245 (negative answer).** There are a topological group `G`, an infinitely
divisible probability `μ` on `G`, `n ≥ 1` and a probability `ν` with `ν^{∗n} = μ` such that `ν`
is not infinitely divisible. -/
theorem main :
    ∃ (G : Type) (_ : Group G) (_ : TopologicalSpace G) (_ : IsTopologicalGroup G)
      (_ : MeasurableSpace G) (_ : BorelSpace G) (μ ν : Measure G) (n : ℕ),
      IsInfDiv μ ∧ 1 ≤ n ∧ IsProbabilityMeasure ν ∧ convPow ν n = μ ∧ ¬ IsInfDiv ν := by
  sorry

end OMA.S_mo_294245

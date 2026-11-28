import Mathlib

/-!
# Randomized Pascal's triangle: the expected average of all the numbers diverges

Source: https://mathoverflow.net/questions/479618
Credit: @tox5tox5

State the problem EXACTLY as the source states it: same quantifiers, same ranges, no simplification.
Do not prove it here: the theorem body stays `sorry`. A person reviews the translation before merging.

The question (MathOverflow 479618, Dan, Sep 2024; first posted on MSE): build a variant of
Pascal's triangle with `1`s down both sides; for each number inside the triangle flip a biased
coin with probability of heads `p`. Heads: write the sum of the two numbers above; tails: write the
absolute value of their difference. What is
`L_p = lim_{n → ∞} (expectation of the arithmetic mean of all numbers in the first n rows)`
as a function of `p`? (`L_1 = ∞`, `L_0 = 0`.)

The page has a partial answer (jvvk, 2026): `L_p = ∞` for every `p > 1 - 1/√2`, and with
computer assistance for `p ≥ 0.232`; "for `0 < p < 0.232` I do not know, though Einar Rødland's
long simulations on MSE suggest `L_p = ∞` for every `p > 0`". This file states that suggested
answer: `L_p = ∞` for every `0 < p ≤ 1`.

Modelling choices:
* Rows are numbered from `0` (the single top `1`); row `n` has `n + 1` entries, the two ends are
  `1`, and each interior entry `j` (`1 ≤ j ≤ n - 1`) of row `n` uses its own coin `C (n, j)`.
  The coins are measurable, mutually independent (`iIndepFun`) Bernoulli(`p`) variables
  (`Pr[C i = true] = p`, `true` = heads) on an arbitrary probability space; coins with indices
  that are not interior positions are unused.
* `mean c N` is the arithmetic mean of all `N (N + 1) / 2` numbers in the first `N` rows, and
  "`L_p = ∞`" is `Tendsto (fun N ↦ 𝔼[mean C N]) atTop atTop`. (Each mean depends on finitely
  many coins and is bounded, so the Bochner integral is the genuine expectation.)
-/

namespace OMA.S_mo_479618

open MeasureTheory ProbabilityTheory Filter

/-- The rule for an interior entry below `a` and `b`: heads gives `a + b`, tails `|a - b|`. -/
def combine (heads : Bool) (a b : ℕ) : ℕ := if heads then a + b else Nat.dist a b

/-- Row `n` of the triangle built with the coin outcomes `c`. -/
def row (c : ℕ × ℕ → Bool) : ℕ → List ℕ
  | 0 => [1]
  | n + 1 => List.ofFn fun j : Fin (n + 2) =>
      if (j : ℕ) = 0 ∨ (j : ℕ) = n + 1 then 1
      else combine (c (n + 1, j)) ((row c n).getD ((j : ℕ) - 1) 0) ((row c n).getD j 0)

/-- The arithmetic mean of all numbers in the first `N` rows (rows `0, …, N - 1`). -/
noncomputable def mean (c : ℕ × ℕ → Bool) (N : ℕ) : ℝ :=
  (∑ n ∈ Finset.range N, ((row c n).sum : ℝ)) / ((N : ℝ) * (N + 1) / 2)

/-- **MathOverflow 479618 (suggested answer).** For every `0 < p ≤ 1`, the expected arithmetic
mean of the numbers in the first `N` rows of the randomized Pascal triangle tends to infinity. -/
theorem main :
    ∀ (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
      (p : ℝ) (C : ℕ × ℕ → Ω → Bool),
      0 < p → p ≤ 1 →
      (∀ i, Measurable (C i)) →
      iIndepFun C μ →
      (∀ i, μ {ω | C i ω = true} = ENNReal.ofReal p) →
      Tendsto (fun N : ℕ => ∫ ω, mean (fun i => C i ω) N ∂μ) atTop atTop := by
  sorry

end OMA.S_mo_479618

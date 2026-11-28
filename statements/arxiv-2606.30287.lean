import Mathlib

/-!
# A weighted Bernoulli sum exceeds its mean with probability at least `p` (for `p ≤ 1/3`)

Source: https://arxiv.org/abs/2606.30287
Credit: @tox5tox5

State the problem EXACTLY as the source states it: same quantifiers, same ranges, no simplification.
Do not prove it here: the theorem body stays `sorry`. A person reviews the translation before merging.

A. Milojević and B. Sudakov, "On the Probability a Weighted Bernoulli Sum Exceeds Its Mean"
(arXiv:2606.30287), Conjecture 1: let `m ≥ 1`, let `w = (w₁, …, w_m)` be positive weights with
`∑ wᵢ = 1`, and let `v₁, …, v_m` be i.i.d. Bernoulli(`p`) random variables. If `X = ∑ wᵢ vᵢ`, then
for all `0 ≤ p ≤ 1/3` we have `P[X ≥ E[X]] ≥ p`. (Here `E[X] = p`; the bound is tight for `m = 1`.
The paper shows it fails for every `p ∈ (1/3, 1)` except `p = 1/2`, and proves it for very small
`p`.) This file states Conjecture 1.

Modelling choices:
* The outcome `v ∈ {0,1}^m` is a function `Fin m → Bool`, with probability
  `∏ᵢ (p if vᵢ else 1 - p)`; the probability of the event is the sum of these weights over the
  outcomes with `∑ wᵢ vᵢ ≥ p` (using `E[X] = p` since `∑ wᵢ = 1`).
-/

namespace OMA.S_arxiv_2606_30287

open Classical

/-- `P[⟨w, v⟩ ≥ p]` for `v` with i.i.d. Bernoulli(`p`) coordinates. -/
noncomputable def probAboveMean (m : ℕ) (w : Fin m → ℝ) (p : ℝ) : ℝ :=
  ∑ v : Fin m → Bool,
    (∏ i, if v i then p else 1 - p) *
      (if p ≤ ∑ i, w i * (if v i then 1 else 0) then 1 else 0)

/-- **Milojević–Sudakov, Conjecture 1.** -/
theorem main :
    ∀ (p : ℝ), 0 ≤ p → p ≤ 1 / 3 →
      ∀ (m : ℕ) (w : Fin m → ℝ), 1 ≤ m → (∀ i, 0 < w i) → ∑ i, w i = 1 →
        p ≤ probAboveMean m w p := by
  sorry

end OMA.S_arxiv_2606_30287

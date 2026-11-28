import Mathlib

/-!
# The maximal probability of `X₁ + X₂ + X₃ < 2X₄` for nonnegative i.i.d. variables

Source: https://arxiv.org/abs/2412.15179
Credit: @tox5tox5

State the problem EXACTLY as the source states it: same quantifiers, same ranges, no simplification.
Do not prove it here: the theorem body stays `sorry`. A person reviews the translation before merging.

P. C. Bellec and T. Fritz, "On maximizing the probability of a linear inequality between iid random
variables" (arXiv:2412.15179). Abstract: for nonnegative i.i.d. `Xᵢ`, "the maximal probability of
the event `X₁ + X₂ + X₃ < 2X₄` lies between 0.400695 and 0.417 … We conjecture the lower bound to be
the exact value." In the paper, `0.400695 ≤ sup_μ P_{μ^{⊗4}}[X₁ + X₂ + X₃ < 2X₄] ≤ 673/1615`, with
`μ` ranging over probability measures on `ℝ₊`, and the lower bound is
`sup_{p ∈ (0,1)} p(2 - p) / (1 + p + p² + p³)` (Proposition 4.1; the maximizer is the root in
`(0, 1)` of `2 - 2p - 3p² - 4p³ + p⁴`, `p ≈ 0.474346`). This file states the conjecture that the
supremum equals this lower bound.

Modelling choices:
* `μ` ranges over probability measures on `ℝ` with `μ (-∞, 0) = 0` (i.e. on `ℝ₊`), and
  `P_{μ^{⊗4}}` is the product measure `Measure.pi` on `Fin 4 → ℝ`; coordinates `0, 1, 2, 3` are
  `X₁, X₂, X₃, X₄`.
* The supremum is taken in `ℝ≥0∞`; the conjectured value is the real supremum of
  `p(2 - p) / (1 + p + p² + p³)` over `p ∈ (0, 1)`, embedded with `ENNReal.ofReal`.
-/

namespace OMA.S_arxiv_2412_15179

open MeasureTheory

/-- `P_{μ^{⊗4}}[X₁ + X₂ + X₃ < 2X₄]`. -/
noncomputable def probIneq (μ : Measure ℝ) : ENNReal :=
  (Measure.pi fun _ : Fin 4 => μ) {x | x 0 + x 1 + x 2 < 2 * x 3}

/-- **Bellec–Fritz, lower bound conjecture.** -/
theorem main :
    (⨆ (μ : Measure ℝ) (_ : IsProbabilityMeasure μ) (_ : μ (Set.Iio 0) = 0), probIneq μ) =
      ENNReal.ofReal
        (sSup ((fun p : ℝ => p * (2 - p) / (1 + p + p ^ 2 + p ^ 3)) '' Set.Ioo 0 1)) := by
  sorry

end OMA.S_arxiv_2412_15179

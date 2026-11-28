import Mathlib

/-!
# Doumas' monotonicity conjecture for `π²/6 + p w_p - p² c_p²`

Source: https://arxiv.org/abs/2202.03713
Credit: @tox5tox5

State the problem EXACTLY as the source states it: same quantifiers, same ranges, no simplification.
Do not prove it here: the theorem body stays `sorry`. A person reviews the translation before merging.

A. V. Doumas, "On the minimum of independent collecting processes via the Stirling numbers of the
second kind" (arXiv:2202.03713). For integers `p ≥ 1` the paper defines the alternating binomial
sums
  `c_p = ∑_{j=0}^{p-1} (-1)^j C(p-1, j) ln(1+j) / (j+1)`,
  `w_p = ∑_{j=0}^{p-1} (-1)^j C(p-1, j) (ln(1+j))² / (j+1)`,
and states Conjecture 2.5: "The sequence `a_p := π²/6 + p w_p - p² c_p²` is decreasing in `p`."
(Remark 2.6 derives from it that `a_p > 0` for all `p ∈ ℕ`; Corollary 2.4 proves
`p² c_p² - p w_p → π²/6`, i.e. `a_p → 0`. Examples: `a_1 = π²/6`, `a_2 = π²/6 - 2 (ln 2)²`.)

Modelling choices:
* `p` ranges over `ℕ` with `p ≥ 1`, as in the paper.
* "Decreasing" is read as strictly decreasing: Remark 2.6 deduces the strict inequality
  `a_p > 0` from the conjecture together with `a_p → 0`, which needs strict monotonicity.
-/

namespace OMA.S_arxiv_2202_03713

/-- `c_p = ∑_{j=0}^{p-1} (-1)^j C(p-1, j) ln(1+j) / (j+1)`. -/
noncomputable def c (p : ℕ) : ℝ :=
  ∑ j ∈ Finset.range p, (-1 : ℝ) ^ j * ((p - 1).choose j : ℝ) * Real.log (1 + j) / (j + 1)

/-- `w_p = ∑_{j=0}^{p-1} (-1)^j C(p-1, j) (ln(1+j))² / (j+1)`. -/
noncomputable def w (p : ℕ) : ℝ :=
  ∑ j ∈ Finset.range p, (-1 : ℝ) ^ j * ((p - 1).choose j : ℝ) * Real.log (1 + j) ^ 2 / (j + 1)

/-- `a_p = π²/6 + p w_p - p² c_p²`. -/
noncomputable def a (p : ℕ) : ℝ := Real.pi ^ 2 / 6 + p * w p - (p : ℝ) ^ 2 * c p ^ 2

/-- **Doumas, Conjecture 2.5.** `a_p` is (strictly) decreasing in `p ≥ 1`. -/
theorem main : ∀ p : ℕ, 1 ≤ p → a (p + 1) < a p := by
  sorry

end OMA.S_arxiv_2202_03713

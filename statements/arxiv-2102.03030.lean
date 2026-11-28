import Mathlib

/-!
# The scaled expected gain of the generalized dice game tends to `√(π/2)`

Source: https://arxiv.org/abs/2102.03030
Credit: @tox5tox5

State the problem EXACTLY as the source states it: same quantifiers, same ranges, no simplification.
Do not prove it here: the theorem body stays `sorry`. A person reviews the translation before merging.

R. Frühwirth, R. Malina and W. Mitaroff, "A new discrete distribution arising from a generalised
random game and its asymptotic properties" (arXiv:2102.03030). Rules: `X₁, X₂, …` are i.i.d.
uniform on `{1, …, n}`; for `k = 1, …, n`, if `X_k ≤ k` the game stops with gain `G_n = k` (at the
first such `k`; `X_n ≤ n` always holds, so the game stops by step `n`). Hence
`P(G_n = k) = (∏_{j=1}^{k-1} P(X_j > j)) · P(X_k ≤ k) = (∏_{j=1}^{k-1} (1 - j/n)) · k/n`, which is the
paper's `p_{k,n} = (k/n^k) (n-1)!/(n-k)!`. Conjecture 3.1 (from a numerical study): `E[G_n/√n]`
converges to `√(π/2)` as `n → ∞`. The paper then proves it (Proposition 4.2, with
`E[G_n]/√n ~ √(π/2) - 1/(3√n)`). This file states that limit.

Modelling choices:
* The law of `G_n` is written explicitly from the rules as above (`pG n k`), and
  `E[G_n] = ∑_{k=1}^n k · P(G_n = k)`.
-/

namespace OMA.S_arxiv_2102_03030

open Filter Topology

/-- `P(G_n = k) = (∏_{j=1}^{k-1} (1 - j/n)) · k/n` for `1 ≤ k ≤ n`. -/
noncomputable def pG (n k : ℕ) : ℝ :=
  (∏ j ∈ Finset.Ico 1 k, (1 - (j : ℝ) / n)) * ((k : ℝ) / n)

/-- `E[G_n]`. -/
noncomputable def EG (n : ℕ) : ℝ := ∑ k ∈ Finset.Icc 1 n, (k : ℝ) * pG n k

/-- **Frühwirth–Malina–Mitaroff, Conjecture 3.1 (proved as Proposition 4.2).** -/
theorem main : Tendsto (fun n : ℕ => EG n / Real.sqrt n) atTop (𝓝 (Real.sqrt (Real.pi / 2))) := by
  sorry

end OMA.S_arxiv_2102_03030

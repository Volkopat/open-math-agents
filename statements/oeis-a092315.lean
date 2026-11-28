import Mathlib

/-!
# OEIS A092315: a closed form for partial sums of the odd harmonic series

Source: https://oeis.org/A092315
`a n` is the smallest `m` such that `∑_{j=0}^{m} 1/(2j+1) > n`. Conjecture (Hasler, 2017):
`a(n) = ⌊exp(2n - γ)/4 + 1/8⌋` for all `n ≥ 1`, with `γ` the Euler–Mascheroni constant.

-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
-/

namespace OMA.S_oeis_a092315

open Real

/-- A092315. -/
noncomputable def a (n : ℕ) : ℕ :=
  sInf {m | (n : ℝ) < ∑ j ∈ Finset.range (m + 1), 1 / (2 * (j : ℝ) + 1)}

theorem main :
    ∀ n : ℕ, 1 ≤ n → a n = ⌊exp (2 * n - eulerMascheroniConstant) / 4 + 1 / 8⌋₊ := by
  sorry

end OMA.S_oeis_a092315

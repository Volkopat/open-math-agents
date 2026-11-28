import Mathlib

/-!
# OEIS A001954: 2-Wythoff positions and tails of ζ(3)

Source: https://oeis.org/A001954
`a n = ⌊(n + 1/2)(2 + √2)⌋` (winning positions in the 2-Wythoff game). Let
`s(n) = ζ(3) - ∑_{k=1}^{n} 1/k³`. Conjecture: for `n ≥ 1`, `s(a(n)) < 1/n² < s(a(n) - 1)`.
(The entry's conjecture continues with a statement about the difference sequence of A049473,
which is not included here.)

-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
-/

namespace OMA.S_oeis_a001954

open Real

/-- A001954. -/
noncomputable def a (n : ℕ) : ℕ := ⌊((n : ℝ) + 1 / 2) * (2 + √2)⌋₊

/-- The tail `ζ(3) - ∑_{k ≤ n} 1/k³`. -/
noncomputable def s (n : ℕ) : ℝ :=
  (riemannZeta 3).re - ∑ k ∈ Finset.Icc 1 n, 1 / (k : ℝ) ^ 3

theorem main :
    ∀ n : ℕ, 1 ≤ n → s (a n) < 1 / (n : ℝ) ^ 2 ∧ 1 / (n : ℝ) ^ 2 < s (a n - 1) := by
  sorry

end OMA.S_oeis_a001954

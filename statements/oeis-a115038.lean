import Mathlib

/-!
# OEIS A115038: smallest `x` such that `x² + prime(n)` is a perfect power

Source: https://oeis.org/A115038
Credit: @PEELY350 (Vihaan Naik; agent: Claude Code, model claude-opus-5-5)

`a(n)` is the smallest `x` such that `x² + prime(n)` is a perfect power
(`5, 1, 2, 1, 4, 6, …`: `5² + 2 = 3³`, `1² + 3 = 2²`).
Conjecture (comment field of the entry): for every prime `p` there are `x, y, n` with
`x² + p = yⁿ`, so that `a` is defined at every index.

Conventions:
* A perfect power is `yⁿ` with exponent `n ≥ 2` (as in the entry's examples); `x` ranges over the
  natural numbers, and `y ≥ 2` holds automatically since `x² + p ≥ 2`.
-/

namespace OMA.S_oeis_a115038

/-- Every prime `p` has `x² + p = yⁿ` for some `x, y` and some exponent `n ≥ 2`. -/
theorem main : ∀ p : ℕ, p.Prime → ∃ x y n : ℕ, 2 ≤ n ∧ x ^ 2 + p = y ^ n := by
  sorry

end OMA.S_oeis_a115038

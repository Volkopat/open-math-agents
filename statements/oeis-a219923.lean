import Mathlib

/-!
# A219923: Number of ways to write n=x+y (x>0, y>0) with x-1, x+1 and 2*x*y+1 all prime.

Source: https://oeis.org/A219923
Credit: @eltociear

`a(n)` (offset 1) counts the ways to write `n = x + y` with `x, y > 0` such that `x - 1`, `x + 1`
and `2xy + 1` are all prime. The entry conjectures (Zhi-Wei Sun):

  a(n) > 0 for all n > 623.

`main` states that such `x`, `y` exist for every `n > 623`. Since `x > 0`, `x - 1` is an exact
natural-number subtraction (and `x - 1` prime forces `x ≥ 3`).
-/

namespace OMA.S_oeis_a219923

/-- The conjecture in OEIS A219923: every `n > 623` is `x + y` with `x, y > 0` and `x - 1`,
`x + 1`, `2xy + 1` all prime. -/
theorem main : ∀ n : ℕ, 623 < n →
    ∃ x y : ℕ, 0 < x ∧ 0 < y ∧ n = x + y ∧
      (x - 1).Prime ∧ (x + 1).Prime ∧ (2 * x * y + 1).Prime := by
  sorry

end OMA.S_oeis_a219923

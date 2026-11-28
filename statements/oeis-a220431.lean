import Mathlib

/-!
# A220431: Number of ways to write n=x+y (x>0, y>0) with 3x-1, 3x+1 and xy-1 all prime

Source: https://oeis.org/A220431
Credit: @niclorusso

Conjecture (Zhi-Wei Sun, in the comments of A220431): a(n)>0 for all n>3. (Verified for n up to
10^9.)

Conventions:
* x, y are positive integers; 3x - 1 >= 2 is exact. For x = y = 1, xy - 1 = 0 is not prime, and the
  natural-number subtraction is exact since xy >= 1.
-/

namespace OMA.S_oeis_a220431

/-- Sun's conjecture on A220431: every `n > 3` is `x + y` with `x, y > 0` such that `3x - 1`,
`3x + 1` and `xy - 1` are all prime. -/
theorem main : ∀ n : ℕ, 3 < n → ∃ x y : ℕ, 0 < x ∧ 0 < y ∧ x + y = n ∧
    (3 * x - 1).Prime ∧ (3 * x + 1).Prime ∧ (x * y - 1).Prime := by
  sorry

end OMA.S_oeis_a220431

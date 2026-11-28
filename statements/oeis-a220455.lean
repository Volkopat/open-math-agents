import Mathlib

/-!
# A220455: Number of ways to write n=x+y (x>0, y>0) with 3x-2, 3x+2 and 2xy+1 all prime

Source: https://oeis.org/A220455
Credit: @niclorusso

Conjecture (Zhi-Wei Sun, in the comments of A220455): a(n)>0 for all n>7. (Verified for n up to
10^9.)

(The comment also records similar conjectures of Sun; only a(n) > 0 for n > 7 is formalized here.)

Conventions:
* x, y are positive integers; 3x - 2 >= 1 is an exact natural-number subtraction.
-/

namespace OMA.S_oeis_a220455

/-- Sun's conjecture on A220455: every `n > 7` is `x + y` with `x, y > 0` such that `3x - 2`,
`3x + 2` and `2xy + 1` are all prime. -/
theorem main : ∀ n : ℕ, 7 < n → ∃ x y : ℕ, 0 < x ∧ 0 < y ∧ x + y = n ∧
    (3 * x - 2).Prime ∧ (3 * x + 2).Prime ∧ (2 * x * y + 1).Prime := by
  sorry

end OMA.S_oeis_a220455

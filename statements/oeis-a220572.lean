import Mathlib

/-!
# A220572: Number of ways to write 2n-1=x+y (x,y>=0) with x^18+3*y^18 prime.

Source: https://oeis.org/A220572
Credit: @eltociear

`a(n)` (offset 1) counts the ways to write `2n - 1 = x + y` with `x, y ≥ 0` such that
`x^18 + 3 y^18` is prime (`a(1) = 1` from `1 = 0 + 1`, since `0^18 + 3·1^18 = 3` is prime and
`1^18 + 3·0^18 = 1` is not). The entry conjectures (Zhi-Wei Sun):

  a(n) > 0 for every n = 1, 2, 3, ....

The comment continues with a stronger "Moreover" claim (odd integers `> 2092` with `x - 3`, `x + 3`
also prime); `main` states only the first sentence, which is the conjecture about this sequence:
for every `n ≥ 1` there are `x, y` with `x + y = 2n - 1` and `x^18 + 3 y^18` prime.
-/

namespace OMA.S_oeis_a220572

/-- The conjecture in OEIS A220572: for every `n ≥ 1`, `2n - 1 = x + y` with `x^18 + 3 y^18`
prime. -/
theorem main : ∀ n : ℕ, 1 ≤ n → ∃ x y : ℕ, x + y = 2 * n - 1 ∧ (x ^ 18 + 3 * y ^ 18).Prime := by
  sorry

end OMA.S_oeis_a220572

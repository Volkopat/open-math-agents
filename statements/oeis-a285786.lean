import Mathlib

/-!
# A285786: a prime p with 2(n-1)^2 < p ≤ 2n^2

Source: https://oeis.org/A285786

A285786 (offset 1): `a(n)` is the number of primes `p` with `2(n-1)^2 < p ≤ 2n^2`:
1, 3, 3, 4, 4, 5, 5, 6, 6, 9, …  For example for `n = 2` the primes in the range `]2, 8]` are
3, 5 and 7, so `a(2) = 3`.

Conjecture (Ralf Steiner, Apr 26 2017, as recorded by Antti Karttunen, May 01 2017):
`a(n) ≥ 1` for all `n`. The entry compares this with Legendre's conjecture that there is always
a prime between `n^2` and `(n+1)^2`.

`a(n) ≥ 1` says exactly that some prime `p` satisfies `2(n-1)^2 < p ≤ 2n^2`, and the conjecture
is stated in that form for every `n ≥ 1`.

Conventions: everything is in `ℕ`; `n - 1` is an exact subtraction for `n ≥ 1` (offset 1).
-/

namespace OMA.S_oeis_a285786

theorem main :
    ∀ n : ℕ, 1 ≤ n → ∃ p : ℕ, Nat.Prime p ∧ 2 * (n - 1) ^ 2 < p ∧ p ≤ 2 * n ^ 2 := by
  sorry

end OMA.S_oeis_a285786

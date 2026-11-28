import Mathlib

/-!
# A108519: a(n) is the smallest natural number m such that (10^n)! - m is prime.

Source: https://oeis.org/A108519
Credit: @gblacher2

Conjecture (comment in A108519): "All terms are noncomposite numbers", that is, for every
`n ≥ 1` the least `m` with `(10^n)! - m` prime is `1` or a prime.

Conventions:
* the offset of A108519 is 1, so `n` ranges over `n ≥ 1` (for `n = 0`, `(10^0)! - m ≤ 1` is never
  prime, so `a 0` is not a term of the sequence);
* `m` ranges over the natural numbers. Subtraction is truncated in `ℕ`, but that changes nothing:
  for `m > (10^n)!` the value `(10^n)! - m` is `0`, which is not prime, so only `m ≤ (10^n)!` can
  occur, and for those the truncated difference is the usual one. Allowing `m = 0` changes nothing
  either, since `(10^n)!` is not prime for `n ≥ 1`;
* "noncomposite" (A008578) means `1` or a prime.

With this definition `a 1 = 11`, and the next terms are 271 and 6701, as in the OEIS data
`11, 271, 6701, 40471`.
-/

namespace OMA.S_oeis_a108519

open Nat

/-- A108519: the smallest natural number `m` such that `(10^n)! - m` is prime. For `n ≥ 1` the set
is nonempty (`m = (10^n)! - 2` gives the prime `2`), so its infimum is its least element. -/
noncomputable def a (n : ℕ) : ℕ :=
  sInf {m : ℕ | ((10 ^ n)! - m).Prime}

/-- The conjecture: every term of A108519 is noncomposite, that is, `1` or a prime. -/
theorem main : ∀ n : ℕ, 1 ≤ n → a n = 1 ∨ (a n).Prime := by
  sorry

end OMA.S_oeis_a108519

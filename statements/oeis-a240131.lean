import Mathlib

/-!
# A240131: least k such that prime(n)^2 + k^2 is prime

Source: https://oeis.org/A240131

A240131 (offset 1): `a(n)` is the least `k` such that `prime(n)^2 + k^2` is prime, or 0 if none:
1, 2, 2, 2, 4, 2, 2, 6, 8, 4, …  For example `prime(3) = 5` and `5^2 + 1^2 = 26` is not prime
but `5^2 + 2^2 = 29` is prime, so `a(3) = 2`.

Conjecture (Robert G. Wilson v, Nov 04 2015): there is always a `k` for any `p_n`. The entry
notes that this has been tested for all primes below `15*10^10`.

The conjecture is stated as: for every prime `p` there is a positive integer `k` with
`p^2 + k^2` prime.

Conventions: quantifying over all `n ≥ 1` is the same as quantifying over all primes
`p = prime(n)`. `k` is positive (the value 0 in the sequence is only the marker for
non-existence, and `k = 0` would give `p^2`, which is not prime).
-/

namespace OMA.S_oeis_a240131

theorem main : ∀ p : ℕ, Nat.Prime p → ∃ k : ℕ, 0 < k ∧ Nat.Prime (p ^ 2 + k ^ 2) := by
  sorry

end OMA.S_oeis_a240131

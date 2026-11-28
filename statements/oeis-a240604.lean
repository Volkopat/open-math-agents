import Mathlib

/-!
# A240604: Primes p with pi(p), pi(2*p), pi(3*p) and pi(4*p) all prime.

Source: https://oeis.org/A240604

Here `pi(x)` is the number of primes not exceeding `x`. The sequence begins
`10909, 67247, 185869, 408379, 511111, …`; for example `pi(10909) = 1327`, `pi(2*10909) = 2447`,
`pi(3*10909) = 3511` and `pi(4*10909) = 4547` are all prime.

Conjecture (Zhi-Wei Sun, Apr 09 2014): for any positive integer `n`, there are infinitely many
primes `p` with `pi(k*p)` prime for all `k = 1, …, n`.

The sequence is the case `n = 4`. The case `n = 1` is known: the primes `p` with `pi(p)` prime
are the primes `prime(prime(m))`, and there are infinitely many of them. The conjecture is open
from `n = 2` on. A numeric check reproduces the entry's first nine terms and finds, among the
primes below `2.2 * 10^6`, 14900 primes for `n = 1`, 1309 for `n = 2`, 117 for `n = 3` and 9 for
`n = 4`.

Encoding:
- `pi` is `Nat.primeCounting`, which counts the primes `≤ x`.
- The statement is the conjecture for every `n ≥ 1`: the set of primes `p` such that
  `Nat.primeCounting (k * p)` is prime for every `k ∈ Finset.Icc 1 n` is infinite.
-/

namespace OMA.S_oeis_a240604

/-- Sun's conjecture: for every `n ≥ 1` there are infinitely many primes `p` such that
`pi (k * p)` is prime for all `k = 1, …, n`. -/
theorem main : ∀ n : ℕ, 1 ≤ n →
    {p : ℕ | p.Prime ∧ ∀ k ∈ Finset.Icc 1 n, (Nat.primeCounting (k * p)).Prime}.Infinite := by
  sorry

end OMA.S_oeis_a240604

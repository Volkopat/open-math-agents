import Mathlib

/-!
# A046869: Good primes (version 1): prime(n)^2 > prime(n-1)*prime(n+1).

Source: https://oeis.org/A046869

Conjecture (Thomas Ordowski, Jul 25 2012): the good primes are exactly the primes `p(n)` such
that `2*p(n) >= p(n-1) + p(n+1)`.

The sequence begins `5, 11, 17, 29, 37, 41, 53, …`. One inclusion is the inequality between the
arithmetic and geometric means: `2*p(n) >= p(n-1) + p(n+1)` gives
`p(n)^2 >= ((p(n-1) + p(n+1))/2)^2 > p(n-1)*p(n+1)`, as `p(n-1) ≠ p(n+1)`. The conjecture is
the other inclusion. The entry's other comments (the asymptotic `a(n) ~ 2*prime(n)`, and a
remark about harmonic means that the entry only calls probable) are not stated here.

Encoding:
- `p k = Nat.nth Nat.Prime k` is the `k`-th prime counted from 0 (`p 0 = 2`), so the OEIS
  `prime(n)` is `p (n - 1)`. A prime `p k` has a predecessor exactly when `k ≥ 1`, which matches
  the OEIS range `n ≥ 2`.
- Both sides are sets of primes, as in the source. Since `p` is injective, the set equality says
  that the two conditions agree at every index `k ≥ 1`.
-/

namespace OMA.S_oeis_a046869

/-- The `k`-th prime, counted from 0: `p 0 = 2`, `p 1 = 3`, `p 2 = 5`, … -/
noncomputable def p (k : ℕ) : ℕ := Nat.nth Nat.Prime k

/-- OEIS A046869, as a set: the primes `p k` (`k ≥ 1`) with `p k ^ 2 > p (k - 1) * p (k + 1)`. -/
def goodPrimes : Set ℕ := {q | ∃ k, 1 ≤ k ∧ q = p k ∧ p (k - 1) * p (k + 1) < p k ^ 2}

/-- Ordowski's conjecture: the good primes are exactly the primes `p k` (`k ≥ 1`) with
`2 * p k ≥ p (k - 1) + p (k + 1)`. -/
theorem main : goodPrimes = {q | ∃ k, 1 ≤ k ∧ q = p k ∧ p (k - 1) + p (k + 1) ≤ 2 * p k} := by
  sorry

end OMA.S_oeis_a046869

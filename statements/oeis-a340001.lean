import Mathlib

/-!
# A340001: Number of ways prime(n) is a sum of five distinct primes.

Source: https://oeis.org/A340001
Credit: @ceejcake

Conjecture (OEIS A340001, comment in the entry by Michel Lagneau): all primes `≥ 43` are the
sum of five distinct primes. In terms of the sequence: `a(n) > 0` whenever `prime(n) ≥ 43`.

Formalization notes:
* The sequence has offset `1`: `prime n` is the `n`-th prime with `prime 1 = 2`, i.e.
  `Nat.nth Nat.Prime (n - 1)` (the `n - 1` is exact for `n ≥ 1`).
* A way of writing `p` as a sum of five distinct primes is an unordered set of five distinct
  primes, i.e. a `Finset` of primes of cardinality `5`, with sum `p` (this matches the OEIS
  example `a(17) = 5` for `59` and the Mathematica program, which counts partitions).
* The search range is lossless: in such a sum the other four summands are primes, hence `≥ 2`,
  so every summand is at most `p - 8 < p`. Therefore all five primes lie in
  `Nat.primesBelow p` (the primes `< p`).
* Initial values: `a(n) = 0` for `n = 1, ..., 13`, and for `n = 14, ..., 25`:
  `a(n) = 1, 1, 2, 5, 6, 11, 14, 16, 25, 29, 39, 57`.
  For example `prime 14 = 43 = 3 + 5 + 7 + 11 + 17` is the only way, so `a 14 = 1`.
-/

namespace OMA.S_oeis_a340001

/-- `prime n` is the `n`-th prime, 1-indexed: `prime 1 = 2`, `prime 2 = 3`, ... -/
noncomputable def prime (n : ℕ) : ℕ := Nat.nth Nat.Prime (n - 1)

/-- The number of ways to write `p` as a sum of five distinct primes, i.e. the number of
`5`-element sets of primes with sum `p` (all such primes are `< p`, see the notes above). -/
def waysFiveDistinctPrimes (p : ℕ) : ℕ :=
  (((Nat.primesBelow p).powersetCard 5).filter fun s => s.sum id = p).card

/-- OEIS A340001: `a n` is the number of ways `prime n` is a sum of five distinct primes. -/
noncomputable def a (n : ℕ) : ℕ := waysFiveDistinctPrimes (prime n)

/-- OEIS A340001 conjecture: every prime `≥ 43` is the sum of five distinct primes,
i.e. `a n > 0` for every `n ≥ 1` with `prime n ≥ 43`. -/
theorem main : ∀ n : ℕ, 1 ≤ n → 43 ≤ prime n → 0 < a n := by
  sorry

end OMA.S_oeis_a340001

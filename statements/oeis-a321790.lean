import Mathlib

/-!
# A321790: the least base above 2 that is a Fermat witness for a base-2 pseudoprime

Source: https://oeis.org/A321790
Credit: @avivorly

A321790: a(n) is the smallest base a > 2 such that a^(k-1) != 1 (mod k), where k = A001567(n), the n-th Fermat
pseudoprime to base 2.

Conjecture (Thomas Ordowski, in the entry): Conjecture: if k = A001567(n) is semiprime, then a(n) < lpf(k).

Conventions:
- A001567, the Fermat pseudoprimes to base 2, is the set of `k : ℕ` with `Nat.FermatPsp k 2`: `k` is not prime,
  `1 < k`, and `k ∣ 2 ^ (k - 1) - 1`, which is `2 ^ (k - 1) ≡ 1 [MOD k]` (`Nat.probablePrime_iff_modEq`).
  Its terms start 341, 561, 645, 1105, 1387, 1729, 1905, 2047, 2465, 2701.
- The index `n` plays no role: the conjecture is a claim about every term `k` of A001567, and `a(n)` is
  `leastBase k` for `k = A001567(n)`.
- `leastBase k` is the least natural number `b > 2` with `¬ b ^ (k - 1) ≡ 1 [MOD k]`, written with `sInf`.
  For every `k ≥ 3` this set is nonempty: it contains `b = k`, as `k ^ (k - 1) ≡ 0 [MOD k]` and `0` is not `1`
  modulo `k > 1`. A term of A001567 is composite, so `k ≥ 4`, and `sInf` is then a true least element (never the
  junk value `sInf ∅ = 0`).
- Semiprime (A001358): `k.primeFactorsList.length = 2`, that is `Ω(k) = 2`: `k = p * q` with primes `p ≤ q`.
  The case `p = q` (a prime square) is included; the Wieferich squares `1093 ^ 2` and `3511 ^ 2` are base-2
  pseudoprimes.
- `lpf(k)`, the least prime factor of `k`, is `k.minFac`.
-/

namespace OMA.S_oeis_a321790

/-- `leastBase k`, the entry's `a(n)` for `k = A001567(n)`: the least `b > 2` with `b ^ (k - 1)` not congruent to
`1` modulo `k`. -/
noncomputable def leastBase (k : ℕ) : ℕ :=
  sInf {b : ℕ | 2 < b ∧ ¬ b ^ (k - 1) ≡ 1 [MOD k]}

theorem main :
    ∀ k : ℕ, Nat.FermatPsp k 2 → k.primeFactorsList.length = 2 → leastBase k < k.minFac := by
  sorry

end OMA.S_oeis_a321790

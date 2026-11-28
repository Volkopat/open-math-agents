import Mathlib

/-!
# A245664: prime-partitionable numbers with a two-prime part

Source: https://oeis.org/A245664
Credit: @avivorly

A245664 lists the prime-partitionable numbers `a(n)` for which there exists a 2-partition of the set of primes `< a(n)`
that has one subset containing two primes only. The entry adds: in this sequence we are interested in
prime-partitionable numbers such that `P1` contains 2 odd primes.

Definition (A059756, after Holsztynski and Strube): a number `n` is prime-partitionable if there is a partition
`{P1, P2}` of the primes less than `n` such that for any composition `n1 + n2 = n`, either there is a prime `p` in `P1`
with `p ∣ n1` or there is a prime `p` in `P2` with `p ∣ n2`.

Conjecture (Christopher Hunt Gribble, in the entry): If `P1 = {p1a, p1b}` with `p1a` and `p1b` odd primes,
`p1a < p1b` and `p1b = 2*k*p1a + 1` for some natural `k` such that `2*k <= p1a - 3` and if `m = p1a + p1b` then `m` is
prime-partitionable and belongs to `{a(n)}`.

Conventions:
- A composition `n1 + n2 = n` has positive parts `n1, n2 ≥ 1`.
- The partition is given by `P1` (a finite set of primes `< n`); `P2` is the set of the other primes `< n`.
  (For `n ≥ 3` both parts of any partition with the property are automatically nonempty: with `P1 = ∅` the composition
  `n2 = 1` fails, and with `P2 = ∅` the composition `n1 = 1` fails.)
- Membership in A245664: the property is symmetric under swapping `P1` with `P2` together with `n1` with `n2`, so the
  subset with two primes only may be taken to be `P1`; following the entry's comment (and its PARI program, which never
  puts `2` in `P1`), its two primes are odd.
- `k` is a natural number; `0 < k` is stated explicitly, and is forced anyway, since `k = 0` gives `p1b = 1`, not prime.
- `2*k <= p1a - 3` is read in `ℕ` (exact here, as an odd prime `p1a` is `≥ 3`); with `k ≥ 1` it forces `p1a ≥ 5`, as in
  the entry's example `a(1) = 16` with the 2-partition `{5, 11}, {2, 3, 7, 13}`.
-/

namespace OMA.S_oeis_a245664

/-- `n` is prime-partitionable: some set `P1` of primes `< n` (with `P2` the other primes `< n`) is such that every
composition `n1 + n2 = n` has a prime of `P1` dividing `n1` or a prime of `P2` dividing `n2`. -/
def PrimePartitionable (n : ℕ) : Prop :=
  ∃ P1 : Finset ℕ, (∀ p ∈ P1, p.Prime ∧ p < n) ∧
    ∀ n1 n2 : ℕ, 1 ≤ n1 → 1 ≤ n2 → n1 + n2 = n →
      (∃ p ∈ P1, p ∣ n1) ∨ (∃ p : ℕ, p.Prime ∧ p < n ∧ p ∉ P1 ∧ p ∣ n2)

/-- `n` is a term of A245664: `n` is prime-partitionable by a partition `{P1, P2}` of the primes `< n` in which `P1`
consists of exactly two odd primes. -/
def InA245664 (n : ℕ) : Prop :=
  ∃ P1 : Finset ℕ, P1.card = 2 ∧ (∀ p ∈ P1, p.Prime ∧ Odd p ∧ p < n) ∧
    ∀ n1 n2 : ℕ, 1 ≤ n1 → 1 ≤ n2 → n1 + n2 = n →
      (∃ p ∈ P1, p ∣ n1) ∨ (∃ p : ℕ, p.Prime ∧ p < n ∧ p ∉ P1 ∧ p ∣ n2)

theorem main :
    ∀ p1a p1b k : ℕ, p1a.Prime → p1b.Prime → Odd p1a → Odd p1b → p1a < p1b → 0 < k →
      p1b = 2 * k * p1a + 1 → 2 * k ≤ p1a - 3 →
        PrimePartitionable (p1a + p1b) ∧ InA245664 (p1a + p1b) := by
  sorry

end OMA.S_oeis_a245664

import Mathlib

/-!
# A259301: frequency of the smaller prime in two-prime prime-partitions

Source: https://oeis.org/A259301
Credit: @avivorly

A259301 counts, over the prime-partitionable numbers `m` that have a 2-partition `{P1, P2}` of the primes `< m` with
`P1` consisting of two primes, how often the smaller prime of `P1` occurs.

Definition (in the entry, after Holsztynski and Strube): a number `n` is prime-partitionable if there is a partition
`{P1, P2}` of the primes less than `n` such that for any composition `n1 + n2 = n`, either there is a prime `p` in `P1`
with `p ∣ n1` or there is a prime `p` in `P2` with `p ∣ n2`.

Conjecture (Christopher Hunt Gribble, in the entry): If `P1 = {p1a, p1b}` with `p1a` and `p1b` odd primes,
`p1a < p1b` and `p1b = 2*k*p1a + 1` for some positive integer `k` such that `2*k <= p1a - 3` and if `m = p1a + p1b`
then `m` is prime-partitionable.

Conventions:
- A composition `n1 + n2 = n` has positive parts `n1, n2 ≥ 1`.
- The partition is given by `P1` (a finite set of primes `< n`); `P2` is the set of the other primes `< n`.
  (For `n ≥ 3` both parts of any partition with the property are automatically nonempty: with `P1 = ∅` the composition
  `n2 = 1` fails, and with `P2 = ∅` the composition `n1 = 1` fails.)
- `2*k <= p1a - 3` is read in `ℕ`; together with `k ≥ 1` it forces `p1a ≥ 5`, as in the entry's examples
  (`p1a = 5, p1b = 11, m = 16`, the first prime-partitionable number).
-/

namespace OMA.S_oeis_a259301

/-- `n` is prime-partitionable: some set `P1` of primes `< n` (with `P2` the other primes `< n`) is such that every
composition `n1 + n2 = n` has a prime of `P1` dividing `n1` or a prime of `P2` dividing `n2`. -/
def PrimePartitionable (n : ℕ) : Prop :=
  ∃ P1 : Finset ℕ, (∀ p ∈ P1, p.Prime ∧ p < n) ∧
    ∀ n1 n2 : ℕ, 1 ≤ n1 → 1 ≤ n2 → n1 + n2 = n →
      (∃ p ∈ P1, p ∣ n1) ∨ (∃ p : ℕ, p.Prime ∧ p < n ∧ p ∉ P1 ∧ p ∣ n2)

theorem main :
    ∀ p1a p1b k : ℕ, p1a.Prime → p1b.Prime → Odd p1a → Odd p1b → p1a < p1b → 0 < k →
      p1b = 2 * k * p1a + 1 → 2 * k ≤ p1a - 3 → PrimePartitionable (p1a + p1b) := by
  sorry

end OMA.S_oeis_a259301

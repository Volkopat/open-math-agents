import Mathlib

/-!
# A059456: Unsafe primes: primes not in A005385.

Source: https://oeis.org/A059456
Credit: @luciusacarr

The entry records the claim (Vincenzo Librandi, Aug 07 2010): From the sequence of prime
numbers, let 2 and remove the first data iteration of 2*p+1; leave 3 and remove the prime data by
the iteration 2*p+1 and we get the sequence. Example for p=2, remove(5,11,23,47); p=3,
remove(7); p=13, p=17, p=19, p=23, remove(47); and so on.

Reading of the source:
* A005385 (safe primes) are the primes `p` such that `(p-1)/2` is also prime; A059456 (unsafe
  primes) are the primes that are not safe primes.
* The sieve: go through the primes in increasing order. Each prime `p` that has not been removed
  is kept, and the iterates `2p+1`, `2(2p+1)+1`, ... of `x ↦ 2x+1` are removed for as long as they
  are prime (the iteration stops at the first composite value: for `p = 2` the removed primes are
  5, 11, 23, 47 and `95` is composite; for `p = 3` only 7 is removed, as `15` is composite, so 31
  is not removed by 3). The `j`-th iterate of `x ↦ 2x+1` starting at `p` is `2^j*(p+1) - 1`.
* So a prime `q` is removed iff there is a kept prime `p < q` and `k ≥ 1` with
  `q = 2^k*(p+1) - 1` and `2^j*(p+1) - 1` prime for every `1 ≤ j ≤ k`; and `q` is kept iff `q`
  is prime and not removed. This is a definition by strong recursion on `q` (`Kept`).
* The claim: the kept numbers are exactly the terms of A059456, i.e. for every `q`,
  `Kept q ↔ (q is prime ∧ q is not a safe prime)`.
-/

namespace OMA.S_oeis_a059456

/-- The numbers kept by the sieve, defined by strong recursion: `q` is kept iff `q` is prime and
there is no kept `p < q` whose `x ↦ 2x+1` iterates `2^j*(p+1) - 1`, `1 ≤ j ≤ k`, are all prime
and end at `q` (for some `k ≥ 1`). -/
def Kept (q : ℕ) : Prop :=
  q.Prime ∧ ¬ ∃ p : Fin q, Kept p.val ∧ ∃ k : ℕ, 1 ≤ k ∧ q = 2 ^ k * (p.val + 1) - 1 ∧
    ∀ j ∈ Finset.Icc 1 k, (2 ^ j * (p.val + 1) - 1).Prime
termination_by q
decreasing_by exact p.isLt

/-- A005385: safe primes `p`, i.e. `p` and `(p-1)/2` are both prime. -/
def IsSafePrime (p : ℕ) : Prop := p.Prime ∧ ((p - 1) / 2).Prime

theorem main : ∀ q : ℕ, Kept q ↔ (q.Prime ∧ ¬ IsSafePrime q) := by
  sorry

end OMA.S_oeis_a059456

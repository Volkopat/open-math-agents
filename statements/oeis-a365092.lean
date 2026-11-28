import Mathlib

/-!
# A365092: the largest `n` with `a(n) = k` is A001144(k)

Source: https://oeis.org/A365092
Credit: @avivorly

A365092 (Jianing Song): Write out the canonical factorization of n and factorize the exponents in the factorization,
the exponents in the factorizations of the exponents, ... until there are only prime numbers left. Replace each p in
the factorization by (p-1)+1 and factorize each p-1 by the same process if p-1 > 1. Continue this process until there
are only 1s left. a(n) is the number of 1s used.
Formula (in the entry): a(2) = 2, a(p) = a(p-1)+1 for primes p > 2; a(p^e) = a(p) + a(e); a(m*n) = a(m) + a(n) for
gcd(m,n) = 1. Example (in the entry): a(1) = 0 since the prime factorization of 1 is empty.

A001144 (N. J. A. Sloane): An exponential function on partitions (next term is 2^512). Comment in that entry
(Franklin T. Adams-Watters): largest number that can be expressed in the form a_1 ^ a_2 ^ ... ^ a_k, where
a_1 + a_2 + ... + a_k = n. Data (offset 1): 1, 2, 3, 4, 9, 27, 512, 134217728.

Conjecture (Jianing Song, in A365092): for k >= 2, the maximum n such that a(n) = k is n = A001144(k).

Conventions:
- `A365092` follows the rules of the entry's programs (PARI, Mathematica): `a 1 = 0`, `a 2 = 2`,
  `a p = a (p - 1) + 1` for primes `p > 2`, and for every other `n ≥ 2`, `a n` is the sum over the primes `p ∣ n` of
  `a p + a e`, with `e` the exponent of `p` in `n`. This is the count of the name: a canonical factorization uses the
  ones of its primes and of its exponents (an exponent `1` is not written, and `a 1 = 0`); the prime `2 = 1 + 1` uses
  two ones and a prime `p > 2` is written `(p - 1) + 1`. The definition reproduces the entry's data `a 1, ..., a 76`
  and its example `a 47029248 = 23`. The recursion is well founded: `p - 1 < p`, and for a composite `n` every prime
  factor and every exponent is `< n`.
- `a 0 = 0` lies outside the offset (1) and plays no role: the conjecture ranges over `n ≥ 1`.
- `A001144 n` follows the comment of A001144: the maximum, over all compositions `a_1 + ... + a_k = n` of `n` into
  positive parts (Mathlib's `Composition n`; the order of the parts matters for a tower), of the tower value
  `a_1 ^ (a_2 ^ (... ^ a_k))`, read right-associated, as the data shows: `512 = 2 ^ (3 ^ 2)` for `n = 7`
  (`tower [] = 1`, so `tower [x] = x`). The formula a(n) = 2^a(n-2) for n >= 7 of A001144 is not used as a definition.
- The maximum n such that a(n) = k is n = A001144(k) is `IsGreatest {n | 1 ≤ n ∧ A365092 n = k} (A001144 k)`:
  `A001144 k` is an index `≥ 1` with `a (A001144 k) = k`, and every `n ≥ 1` with `a n = k` is at most `A001144 k`.
-/

namespace OMA.S_oeis_a365092

/-- A365092: `a 1 = 0`, `a 2 = 2`, `a p = a (p - 1) + 1` for primes `p > 2`, and for the other `n ≥ 2`,
`a n = ∑ p ∈ n.primeFactors, (a p + a (n.factorization p))`. -/
def A365092 (n : ℕ) : ℕ :=
  if h1 : n ≤ 1 then 0
  else if n = 2 then 2
  else if hp : n.Prime then A365092 (n - 1) + 1
  else ∑ q ∈ n.primeFactors.attach, (A365092 q + A365092 (n.factorization q))
termination_by n
decreasing_by
  all_goals first
    | omega
    | exact Nat.factorization_lt _ (by omega)
    | exact lt_of_le_of_ne (Nat.le_of_dvd (by omega) (Nat.dvd_of_mem_primeFactors q.2))
        (fun h => hp (h ▸ Nat.prime_of_mem_primeFactors q.2))

/-- The right-associated power tower `tower [a₁, a₂, ..., a_k] = a₁ ^ (a₂ ^ (... ^ a_k))`; `tower [] = 1`. -/
def tower : List ℕ → ℕ
  | [] => 1
  | x :: l => x ^ tower l

/-- A001144: the largest tower value `a₁ ^ a₂ ^ ... ^ a_k` over the compositions `a₁ + ... + a_k = n` of `n`. -/
def A001144 (n : ℕ) : ℕ := Finset.univ.sup fun c : Composition n => tower c.blocks

theorem main : ∀ k : ℕ, 2 ≤ k → IsGreatest {n : ℕ | 1 ≤ n ∧ A365092 n = k} (A001144 k) := by
  sorry

end OMA.S_oeis_a365092

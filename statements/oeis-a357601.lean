import Mathlib

/-!
# A357601: a Doudna-type recursion on the number of divisors

Source: https://oeis.org/A357601
Credit: @avivorly

A357601 (offset 1): For n a power of 2, a(n) = n; otherwise, if 2^m is the greatest power of 2 not exceeding n
and if k = n-2^m, then a(n) is the smallest number having d(a(k))+1 divisors which has not occurred earlier
(d is the divisor counting function A000005).

Claim in the entry: Conjectured to be permutation of the positive integers in which the primes appear in
natural order.

Conventions:
- `pre n` is the list `[a(1), ..., a(n)]` of the first `n` terms, and `a n` is its last entry. So `a 0 = 0` is a
  junk value outside the offset; only `n ≥ 1` is used.
- For the index `N = n + 1`, `Nat.log 2 N` is the `m` with `2^m ≤ N < 2^(m+1)`, so `2 ^ Nat.log 2 N` is the
  greatest power of 2 not exceeding `N`, and `N` is a power of 2 exactly when `N = 2 ^ Nat.log 2 N`.
- Otherwise `k = N - 2 ^ Nat.log 2 N` satisfies `1 ≤ k ≤ n`, and `a(k)` is the entry `(pre n).getD (k - 1) 0`
  of `pre n` (lists are indexed from 0).
- `d(x)` is `x.divisors.card` (`Nat.divisors`). Has not occurred earlier means `v ∉ pre n`.
- The smallest such number is `sInf` of the set of naturals `v` with `v.divisors.card = d(a(k)) + 1` and
  `v ∉ pre n`. This set is never empty: every term is positive (by induction on the index), so
  `d(a(k)) + 1 = t + 1` with `t ≥ 1`, and for a prime `q` larger than every entry of `pre n` the number `q^t`
  has `t + 1` divisors and is larger than every entry, so it is not in `pre n` (a prime `q` merely absent from
  `pre n` is not enough, as `q^t` may be present). So `sInf` is its least element. Only positive `v` can
  qualify: `0` has no divisors in Mathlib (`Nat.divisors 0 = ∅`), while `d(a(k)) + 1 ≥ 1`.
- A permutation of the positive integers (offset 1, terms `≥ 1`) means: every `a n` with `n ≥ 1` is `≥ 1`, `a`
  is injective on the indices `n ≥ 1`, and every `m ≥ 1` equals `a n` for some `n ≥ 1`.
- The primes appear in natural order: whenever `1 ≤ i < j` and `a i`, `a j` are both prime, `a i < a j`.
-/

namespace OMA.S_oeis_a357601

/-- `pre n` is the list `[a(1), ..., a(n)]` of the first `n` terms. The entry for the index `N = n + 1` is `N`
when `N` is a power of 2, and otherwise the least `v` with `d(a(k)) + 1` divisors that is not among the first
`n` terms, where `k = N - 2 ^ Nat.log 2 N` and `a(k) = (pre n).getD (k - 1) 0`. -/
noncomputable def pre : ℕ → List ℕ
  | 0 => []
  | n + 1 => pre n ++
      [if n + 1 = 2 ^ Nat.log 2 (n + 1) then n + 1 else
        sInf {v : ℕ | v.divisors.card =
          ((pre n).getD (n + 1 - 2 ^ Nat.log 2 (n + 1) - 1) 0).divisors.card + 1 ∧ v ∉ pre n}]

/-- `a n` is the `n`-th term (offset 1): the last entry of `pre n`. -/
noncomputable def a (n : ℕ) : ℕ := (pre n).getLastD 0

theorem main :
    (∀ n : ℕ, 1 ≤ n → 1 ≤ a n) ∧
    (∀ i j : ℕ, 1 ≤ i → 1 ≤ j → a i = a j → i = j) ∧
    (∀ m : ℕ, 1 ≤ m → ∃ n : ℕ, 1 ≤ n ∧ a n = m) ∧
    (∀ i j : ℕ, 1 ≤ i → i < j → (a i).Prime → (a j).Prime → a i < a j) := by
  sorry

end OMA.S_oeis_a357601

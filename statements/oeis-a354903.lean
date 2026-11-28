import Mathlib

/-!
# A354903: the number of divisors of each term is prime to the previous term

Source: https://oeis.org/A354903
Credit: @avivorly

A354903 (offset 1): Lexicographically earliest infinite sequence of distinct positive integers such that the
number of divisors of a(n+1) is prime to a(n).

Claim in the entry: Conjectured to be a permutation of the positive integers in which primes appear in natural
order.

Conventions:
- `pre n` is the list `[a(1), ..., a(n)]` of the first `n` terms, and `a n` is its last entry. So `a 0 = 0` is a
  junk value outside the offset; only `n ≥ 1` is used.
- The number of divisors of `k` is `k.divisors.card`, and `x` is prime to `y` means `Nat.Coprime x y`, that is
  `gcd(x, y) = 1`.
- The greedy rule: `pre 0 = []`, and the next term `a(n+1)` is the least `k` with `1 ≤ k`, `k ∉ pre n` and
  `Nat.Coprime k.divisors.card c`, where `c = (pre n).getLastD 1` is the previous term `a(n)` when `n ≥ 1`; it is
  written as `sInf` of that set of naturals. Positivity is `1 ≤ k`; distinctness is `k ∉ pre n`.
- The first term has no previous term, so no condition applies to it; the default `1` in `getLastD 1` encodes
  this (every number is prime to `1`). So `a(1) = 1` and then `a(2) = 2`, as the entry's comment says (1, 2 are
  the earliest consecutive pair of numbers satisfying the definition).
- Why the greedy rule gives the lexicographically earliest infinite sequence: every finite list of distinct
  positive terms whose last entry is `c ≥ 1` can be extended. Take a prime `s` not dividing `c` (any prime
  `s > c`) and a prime `q` larger than every entry of the list; then `k = q^(s-1)` is not in the list, it has
  exactly `s` divisors, and `s` is prime to `c` (this is the argument of the entry's second comment). So the set
  above is never empty and `sInf` is its least element; in particular every term is `≥ 1`, so the next `c` is
  again `≥ 1`. As every admissible prefix extends, no prefix is a dead end, and taking the least admissible term
  at each step gives the lexicographically earliest infinite sequence.
- A permutation of the positive integers (offset 1, terms `≥ 1`) means: every `a n` with `n ≥ 1` is `≥ 1`, `a`
  is injective on the indices `n ≥ 1`, and every `m ≥ 1` equals `a n` for some `n ≥ 1`. The primes appear in
  natural order: if `1 ≤ i < j` and `a i` and `a j` are both prime, then `a i < a j`.
-/

namespace OMA.S_oeis_a354903

/-- `pre n` is the list `[a(1), ..., a(n)]` of the first `n` terms of the greedy sequence. -/
noncomputable def pre : ℕ → List ℕ
  | 0 => []
  | n + 1 => pre n ++
      [sInf {k : ℕ | 1 ≤ k ∧ k ∉ pre n ∧ Nat.Coprime k.divisors.card ((pre n).getLastD 1)}]

/-- `a n` is the `n`-th term (offset 1): the last entry of `pre n`. -/
noncomputable def a (n : ℕ) : ℕ := (pre n).getLastD 0

theorem main :
    (∀ n : ℕ, 1 ≤ n → 1 ≤ a n) ∧
    (∀ i j : ℕ, 1 ≤ i → 1 ≤ j → a i = a j → i = j) ∧
    (∀ m : ℕ, 1 ≤ m → ∃ n : ℕ, 1 ≤ n ∧ a n = m) ∧
    (∀ i j : ℕ, 1 ≤ i → i < j → (a i).Prime → (a j).Prime → a i < a j) := by
  sorry

end OMA.S_oeis_a354903

import Mathlib

/-!
# A287639: consecutive sums of binary weight at least 10

Source: https://oeis.org/A287639
Credit: @avivorly

A287639 (offset 1): Lexicographically earliest sequence of distinct positive terms such that the sum of two
consecutive terms has Hamming weight >= 10.

Claim in the entry: Conjecturally, this is a permutation of the natural numbers.

Conventions:
- `wt s` is the binary Hamming weight of `s`: the number of digits `1` in the base-2 expansion `Nat.digits 2 s`.
- `pre n` is the list `[a(1), ..., a(n)]` of the first `n` terms, and `a n` is its last entry. So `a 0 = 0` is a
  junk value outside the offset; only `n ≥ 1` is used.
- The greedy rule: `pre 1 = [1]`, and for `n ≥ 1` the next term `a(n+1)` is the least `k` with `1 ≤ k`,
  `k ∉ pre n` and `10 ≤ wt (a(n) + k)`, written as `sInf` of that set of naturals (`(pre n).getLastD 0` is `a(n)`).
  Positivity is `1 ≤ k`; distinctness is `k ∉ pre n`.
- Why the greedy rule gives the lexicographically earliest sequence: `a(1) = 1` is the least positive term. Every
  finite list of distinct positive terms can be extended: for `x` its last entry and `K` large, `2^K - 1 - x` is
  positive, is not in the list, and `wt (x + (2^K - 1 - x)) = wt (2^K - 1) = K ≥ 10`. So the set above is never
  empty, and `sInf` is its least element. When every admissible prefix extends, taking the least admissible term at
  each step gives the lexicographically earliest infinite sequence.
- A permutation of the natural numbers (offset 1, terms `≥ 1`) means: every `a n` with `n ≥ 1` is `≥ 1`, `a` is
  injective on the indices `n ≥ 1`, and every `m ≥ 1` equals `a n` for some `n ≥ 1`.
-/

namespace OMA.S_oeis_a287639

/-- Binary Hamming weight: the number of ones among the base-2 digits of `s`. -/
def wt (s : ℕ) : ℕ := (Nat.digits 2 s).count 1

/-- `pre n` is the list `[a(1), ..., a(n)]` of the first `n` terms of the greedy sequence. -/
noncomputable def pre : ℕ → List ℕ
  | 0 => []
  | 1 => [1]
  | n + 2 => pre (n + 1) ++
      [sInf {k : ℕ | 1 ≤ k ∧ k ∉ pre (n + 1) ∧ 10 ≤ wt ((pre (n + 1)).getLastD 0 + k)}]

/-- `a n` is the `n`-th term (offset 1): the last entry of `pre n`. -/
noncomputable def a (n : ℕ) : ℕ := (pre n).getLastD 0

theorem main :
    (∀ n : ℕ, 1 ≤ n → 1 ≤ a n) ∧
    (∀ i j : ℕ, 1 ≤ i → 1 ≤ j → a i = a j → i = j) ∧
    (∀ m : ℕ, 1 ≤ m → ∃ n : ℕ, 1 ≤ n ∧ a n = m) := by
  sorry

end OMA.S_oeis_a287639

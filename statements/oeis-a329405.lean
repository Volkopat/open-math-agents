import Mathlib

/-!
# A329405: no prime among the pairwise sums of three consecutive terms

Source: https://oeis.org/A329405
Credit: @avivorly

A329405 (offset 1): Among the pairwise sums of any three consecutive terms there is no prime: lexicographically
earliest such sequence of distinct positive integers.

Claim in the entry: Conjectured to be a permutation of the positive integers.

Conventions:
- `pre n` is the list `[a(1), ..., a(n)]` of the first `n` terms, and `a n` is its last entry. So `a 0 = 0` is a
  junk value outside the offset; only `n ≥ 1` is used.
- The three pairwise sums of the consecutive terms `a(i), a(i+1), a(i+2)` are `a(i) + a(i+1)`, `a(i) + a(i+2)`
  and `a(i+1) + a(i+2)`. So no such sum is prime exactly when `a(i) + a(j)` is not prime whenever
  `1 ≤ j - i ≤ 2` (the equivalent form given in the entry): each new term is checked against the (at most) two
  terms before it.
- The greedy rule: `pre 0 = []`, and the next term `a(n+1)` is the least `k` with `1 ≤ k`, `k ∉ pre n` and
  `x + k` not prime for every `x` in `(pre n).drop (n - 2)`, the last (at most two) entries of `pre n`; it is
  written as `sInf` of that set of naturals. Positivity is `1 ≤ k`; distinctness is `k ∉ pre n`.
- Why the greedy rule gives the lexicographically earliest sequence: `a(1) = 1` is the least positive term. Every
  finite list of `n` distinct positive terms can be extended: let `x` and `y` be its last two entries (a shorter
  list has fewer conditions). The numbers `k ≥ 6` with `k ≡ x (mod 2)` and `k ≡ -y (mod 3)` form one residue
  class mod 6; for each of them `x + k` is even and greater than 2 and `y + k` is divisible by 3 and greater
  than 3, so neither is prime; and the first `n + 1` of them are not all in the list. So the set above is never
  empty, and `sInf` is its least element. When every admissible prefix extends, taking the least admissible
  term at each step gives the lexicographically earliest infinite sequence.
- A permutation of the positive integers (offset 1, terms `≥ 1`) means: every `a n` with `n ≥ 1` is `≥ 1`, `a`
  is injective on the indices `n ≥ 1`, and every `m ≥ 1` equals `a n` for some `n ≥ 1`.
-/

namespace OMA.S_oeis_a329405

/-- `pre n` is the list `[a(1), ..., a(n)]` of the first `n` terms of the greedy sequence. -/
noncomputable def pre : ℕ → List ℕ
  | 0 => []
  | n + 1 => pre n ++
      [sInf {k : ℕ | 1 ≤ k ∧ k ∉ pre n ∧ ∀ x ∈ (pre n).drop (n - 2), ¬ (x + k).Prime}]

/-- `a n` is the `n`-th term (offset 1): the last entry of `pre n`. -/
noncomputable def a (n : ℕ) : ℕ := (pre n).getLastD 0

theorem main :
    (∀ n : ℕ, 1 ≤ n → 1 ≤ a n) ∧
    (∀ i j : ℕ, 1 ≤ i → 1 ≤ j → a i = a j → i = j) ∧
    (∀ m : ℕ, 1 ≤ m → ∃ n : ℕ, 1 ≤ n ∧ a n = m) := by
  sorry

end OMA.S_oeis_a329405

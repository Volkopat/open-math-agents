import Mathlib

/-!
# A329450: neither a(n) + a(n+1) nor a(n) + a(n+2) is prime

Source: https://oeis.org/A329450
Credit: @avivorly

A329450 (offset 0): Lexicographically earliest sequence of distinct nonnegative integers such that neither
a(n) + a(n+1) nor a(n) + a(n+2) is prime for any n.

Claim in the entry: Conjectured to be a permutation of the nonnegative integers.

Conventions:
- `pre n` is the list `[a(0), ..., a(n-1)]` of the first `n` terms, and `a n` is the last entry of `pre (n + 1)`
  (offset 0).
- The condition says that `a(i) + a(j)` is not prime whenever `1 ≤ j - i ≤ 2`: each new term is checked against
  the (at most) two terms before it.
- The greedy rule: `pre 0 = []`, and the next term `a(n)` is the least `k` with `k ∉ pre n` and `x + k` not prime
  for every `x` in `(pre n).drop (n - 2)`, the last (at most two) entries of `pre n`; it is written as `sInf` of
  that set of naturals. Distinctness is `k ∉ pre n`; nonnegative integers are the naturals `ℕ`.
- Why the greedy rule gives the lexicographically earliest sequence: `a(0) = 0` is the least nonnegative term.
  Every finite list of `n` distinct naturals can be extended: let `x` and `y` be its last two entries (a shorter
  list has fewer conditions). The numbers `k ≥ 6` with `k ≡ x (mod 2)` and `k ≡ -y (mod 3)` form one residue
  class mod 6; for each of them `x + k` is even and greater than 2 and `y + k` is divisible by 3 and greater
  than 3, so neither is prime; and the first `n + 1` of them are not all in the list. So the set above is never
  empty, and `sInf` is its least element. When every admissible prefix extends, taking the least admissible
  term at each step gives the lexicographically earliest infinite sequence.
- A permutation of the nonnegative integers means: `a : ℕ → ℕ` is injective and surjective.
-/

namespace OMA.S_oeis_a329450

/-- `pre n` is the list `[a(0), ..., a(n-1)]` of the first `n` terms of the greedy sequence. -/
noncomputable def pre : ℕ → List ℕ
  | 0 => []
  | n + 1 => pre n ++
      [sInf {k : ℕ | k ∉ pre n ∧ ∀ x ∈ (pre n).drop (n - 2), ¬ (x + k).Prime}]

/-- `a n` is the `n`-th term (offset 0): the last entry of `pre (n + 1)`. -/
noncomputable def a (n : ℕ) : ℕ := (pre (n + 1)).getLastD 0

theorem main : Function.Injective a ∧ Function.Surjective a := by
  sorry

end OMA.S_oeis_a329450

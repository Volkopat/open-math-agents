import Mathlib

/-!
# A280172: Lexicographically earliest table of positive integers read by antidiagonals such that no
row or column contains a repeated term.

Source: https://oeis.org/A280172
Credit: @Squee451

Data, by antidiagonals: 1; 2, 2; 3, 1, 3; 4, 4, 4, 4; 5, 3, 1, 3, 5; 6, 6, 2, 2, 6, 6; ...

The entry's comments contain two conjectures:
* Conjecture: The (2^k)-th antidiagonal consists entirely of 2^k.
* Conjecture: T(2n, k) = 2 * T(n, ceiling(k/2)), n >= 1, 1 <= k <= 2n.
  (E.g. row 5: 5, 3, 1, 3, 5; row 10: 10, 10, 6, 6, 2, 2, 6, 6, 10, 10.)
Here T(n, k) is the k-th term of the n-th antidiagonal (rows of the triangle), both counted from 1.

Conventions.
* The table is a function `G i j` with rows `i` and columns `j` counted from 0. Read by
  antidiagonals, every earlier entry of row `i` (columns `< j`) and of column `j` (rows `< i`) has
  already been written when `G i j` is chosen, and entries of the same antidiagonal never share a
  row or a column. Since any positive integer may be used, a least admissible choice can always be
  continued, so the lexicographically earliest table is the one in which every entry is the least
  positive integer that does not already occur to its left in its row or above it in its column.
  `Greedy G` says exactly that.
* The n-th antidiagonal (n ≥ 1) consists of the entries `G i j` with `i + j = n - 1`; its k-th term
  (1 ≤ k ≤ n) is `T G n k = G (k-1) (n-k)`. The first conjecture is stated for all k ≥ 0 (the first
  antidiagonal is the single entry 1 = 2^0). `(k + 1) / 2` is the ceiling of `k / 2`.
* The statement asserts that a greedy table exists, and the two conjectures for every greedy table
  (there is in fact exactly one).
-/

namespace OMA.S_oeis_a280172

/-- `v` is a positive integer that does not occur earlier in row `i` or earlier in column `j`. -/
def Available (G : ℕ → ℕ → ℕ) (i j v : ℕ) : Prop :=
  0 < v ∧ (∀ k, k < j → G i k ≠ v) ∧ (∀ k, k < i → G k j ≠ v)

/-- Every entry is the least positive integer not occurring earlier in its row or its column. -/
def Greedy (G : ℕ → ℕ → ℕ) : Prop :=
  ∀ i j, IsLeast {v : ℕ | Available G i j v} (G i j)

/-- The `k`-th term of the `n`-th antidiagonal, both counted from 1. -/
def T (G : ℕ → ℕ → ℕ) (n k : ℕ) : ℕ := G (k - 1) (n - k)

theorem main :
    (∃ G : ℕ → ℕ → ℕ, Greedy G) ∧
    ∀ G : ℕ → ℕ → ℕ, Greedy G →
      (∀ e i j : ℕ, i + j = 2 ^ e - 1 → G i j = 2 ^ e) ∧
      (∀ n k : ℕ, 1 ≤ n → 1 ≤ k → k ≤ 2 * n → T G (2 * n) k = 2 * T G n ((k + 1) / 2)) := by
  sorry

end OMA.S_oeis_a280172

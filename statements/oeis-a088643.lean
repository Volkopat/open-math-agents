import Mathlib

/-!
# A088643

Source: https://oeis.org/A088643
Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

Row `n ≥ 1` starts with `n`; the next term is always the largest `m` with `1 ≤ m < n` that has
not yet appeared in the row and such that `m` plus the previous term is prime; stop when no such
`m` exists. Conjecture (OEIS, verified for `n ≤ 400000`): row `n` is always a permutation of
`{1, …, n}`.

## Encoding

* `next n r` is the largest admissible `m` for the current row `r` (or `none`); the row is built
  by at most `n` steps (a row has at most `n` distinct entries), definition checked against the
  OEIS terms.
* Rows never repeat entries, so "permutation of `{1, …, n}`" is `(row n).toFinset = [1, n]`.
-/

namespace OMA.S_oeis_a088643

/-- The largest `m < n`, `m ≥ 1`, not in `r`, with `m + last r` prime. -/
def next (n : ℕ) (r : List ℕ) : Option ℕ :=
  ((List.range n).reverse.filter fun m =>
    decide (1 ≤ m ∧ m ∉ r ∧ (m + r.getLast!).Prime)).head?

/-- Extend the row `r` by at most `fuel` greedy steps. -/
def build (n : ℕ) : ℕ → List ℕ → List ℕ
  | 0, r => r
  | fuel + 1, r =>
    match next n r with
    | none => r
    | some m => build n fuel (r ++ [m])

/-- Row `n` of the triangle. -/
def row (n : ℕ) : List ℕ := build n n [n]

theorem main : ∀ n : ℕ, 1 ≤ n → (row n).toFinset = Finset.Icc 1 n := by
  sorry

end OMA.S_oeis_a088643

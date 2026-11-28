import Mathlib

/-!
# OEIS A007063: is the diagonal of Kimberling's expulsion array a permutation?

Source: https://oeis.org/A007063
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

Conjecture (Kimberling, 1992): the main diagonal `1, 3, 5, 4, 10, 7, 15, …` of Kimberling's
expulsion array (A035486) is a permutation of the positive integers.

The array (rows and columns indexed from 1). Row 1 is `1, 2, 3, …`. Row `i+1` is obtained from
row `i = (t₁, t₂, …)` by expelling the diagonal term `tᵢ` and listing
`t_{i+1}, t_{i-1}, t_{i+2}, t_{i-2}, …, t_{2i-1}, t₁, t_{2i}, t_{2i+1}, …`; that is,
entry `j` of row `i+1` is `t_{i+k}` for `j = 2k-1 ≤ 2i-2`, `t_{i-k}` for `j = 2k ≤ 2i-2`, and
`t_{j+1}` for `j ≥ 2i-1`. (This reproduces the data `1, 3, 5, 4, 10, 7, 15, 8, …`.)
Rows are encoded as functions on `ℕ` with column `j` at index `j - 1`.
-/

namespace OMA.S_oeis_a007063

/-- Row `i + 1` from row `i` (0-indexed columns; `i ≥ 1` is the row number). -/
def nextRow (i : ℕ) (t : ℕ → ℕ) : ℕ → ℕ := fun c =>
  let j := c + 1
  if j ≤ 2 * i - 2 then
    (if j % 2 = 1 then t (i + (j + 1) / 2 - 1) else t (i - j / 2 - 1))
  else t (j + 1 - 1)

/-- Row `i` of the expulsion array (`i ≥ 1`; row `0` is unused and equals row 1). -/
def row : ℕ → ℕ → ℕ
  | 0 => fun c => c + 1
  | 1 => fun c => c + 1
  | (i + 2) => nextRow (i + 1) (row (i + 1))

/-- The main diagonal `a(i) = T(i, i)`, `i ≥ 1`. -/
def diag (i : ℕ) : ℕ := row i (i - 1)

/-- Kimberling's conjecture: `i ↦ T(i, i)` is a bijection of the positive integers. -/
theorem main :
    Set.BijOn diag {i : ℕ | 1 ≤ i} {n : ℕ | 1 ≤ n} := by
  sorry

end OMA.S_oeis_a007063

import Mathlib

/-!
# OEIS A184063

A184063: Number of `(n + 1) × 2` binary arrays with rows and columns in
(lexicographically) nondecreasing order and with no `2 × 2` subblock sum differing
from a horizontal or vertical neighbor subblock sum by more than one.

Conjectures from Colin Barker (Apr 11 2018):
- `a(n) = (n^3 + 6 * n^2 + 5 * n + 24) / 6` for `n > 1`,
- `a(n) = 4 * a(n - 1) - 6 * a(n - 2) + 4 * a(n - 3) - a(n - 4)` for `n > 5`.

Note: OEIS A184063 has offset 1 and data
`7, 11, 20, 34, 54, 81, 116, 160, 214, 279, ...`.
Since each array has width 2, there is one `2 × 2` subblock per adjacent pair of
rows, so only vertical neighbor `2 × 2` subblocks exist.

Reference: https://oeis.org/A184063
-/

namespace OMA.S_oeis_a184063

/-- Lexicographic nondecreasing order on rows of an `(n + 1) × 2` binary array:
for each `i : Fin n`, row `i` is `≤` row `i + 1` lexicographically. -/
def rowsNondecreasing {n : ℕ} (A : Fin (n + 1) → Fin 2 → Bool) : Prop :=
  ∀ i : Fin n,
    (A i.castSucc 0 = false ∧ A i.succ 0 = true) ∨
    (A i.castSucc 0 = A i.succ 0 ∧ (A i.castSucc 1 = true → A i.succ 1 = true))

/-- Lexicographic nondecreasing order on the two columns of an `(n + 1) × 2` binary
array: column `0` is `≤` column `1` lexicographically, meaning either the columns
are equal or at the first row where they differ column `0` is `false` and column `1`
is `true`. -/
def colsNondecreasing {n : ℕ} (A : Fin (n + 1) → Fin 2 → Bool) : Prop :=
  (∀ r : Fin (n + 1), A r 0 = A r 1) ∨
  ∃ r : Fin (n + 1), (∀ r' : Fin (n + 1), r' < r → A r' 0 = A r' 1) ∧
    A r 0 = false ∧ A r 1 = true

/-- Sum of the `i`-th `2 × 2` subblock (rows `i` and `i + 1`). -/
def subblockSum {n : ℕ} (A : Fin (n + 1) → Fin 2 → Bool) (i : Fin n) : ℕ :=
  (A i.castSucc 0).toNat + (A i.castSucc 1).toNat +
  (A i.succ 0).toNat + (A i.succ 1).toNat

/-- Adjacent `2 × 2` subblock sums differ by at most `1`. -/
def smoothSubblocks {n : ℕ} (A : Fin (n + 1) → Fin 2 → Bool) : Prop :=
  ∀ i j : Fin n, i.val + 1 = j.val →
    subblockSum A i ≤ subblockSum A j + 1 ∧ subblockSum A j ≤ subblockSum A i + 1

/-- An `(n + 1) × 2` binary array is valid if its rows and columns are in
nondecreasing lexicographic order and adjacent `2 × 2` subblock sums differ by at most `1`. -/
def isValid (n : ℕ) (A : Fin (n + 1) → Fin 2 → Bool) : Prop :=
  rowsNondecreasing A ∧ colsNondecreasing A ∧ smoothSubblocks A

/-- `a n` is the number of valid `(n + 1) × 2` binary arrays. -/
noncomputable def a (n : ℕ) : ℕ :=
  Nat.card {A : Fin (n + 1) → Fin 2 → Bool // isValid n A}

/-- Colin Barker's conjectures for OEIS A184063:
`a(n) = (n^3 + 6*n^2 + 5*n + 24) / 6` for `n > 1` and
`a(n) = 4*a(n - 1) - 6*a(n - 2) + 4*a(n - 3) - a(n - 4)` for `n > 5`. -/
theorem main :
    (∀ n : ℕ, 1 < n → 6 * a n = n ^ 3 + 6 * n ^ 2 + 5 * n + 24) ∧
    (∀ n : ℕ, 5 < n →
      (a n : ℤ) = 4 * a (n - 1) - 6 * a (n - 2) + 4 * a (n - 3) - a (n - 4)) := by
  sorry

end OMA.S_oeis_a184063

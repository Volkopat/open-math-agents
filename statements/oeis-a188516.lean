import Mathlib

/-!
# A188516: Number of nX2 binary arrays without the pattern 1 1 0 diagonally, vertically or horizontally.

Source: https://oeis.org/A188516 (conjecture by Clark Kimberling, Jun 21 2016)

An `n X k` binary array is `f : Fin n → Fin k → Bool` (row index first; `true` is 1).
`cell f i j` is the entry in row `i` and column `j` when these are in range (and `false`
otherwise; it is only read at in-range positions). The pattern 1 1 0 occurs at three positions
if all of them are in range and the entries there are 1, 1, 0 in this order. The pattern is read
in the direction of increasing row index (vertically), of increasing column index (horizontally),
along a diagonal (row and column increasing) and along an antidiagonal (row increasing, column
decreasing). `a(n)` (offset 1) counts the `n X 2` arrays where the pattern occurs in none of these
four ways.

The conjecture, stated for `n >= 1` (the offset), in `ℕ` (where `Nat.fib (n + 3) >= 1`):
a(n) = (F(n+3) - 1)^2, where F = A000045 (Fibonacci numbers).
-/

namespace OMA.S_oeis_a188516

/-- The entry in row `i`, column `j`, or `false` when out of range. -/
def cell {n k : ℕ} (f : Fin n → Fin k → Bool) (i j : ℕ) : Bool :=
  if h : i < n ∧ j < k then f ⟨i, h.1⟩ ⟨j, h.2⟩ else false

/-- The pattern 1 1 0 occurs at the in-range positions `(i0, j0), (i1, j1), (i2, j2)`. -/
def occurs {n k : ℕ} (f : Fin n → Fin k → Bool) (i0 j0 i1 j1 i2 j2 : ℕ) : Prop :=
  i0 < n ∧ j0 < k ∧ i1 < n ∧ j1 < k ∧ i2 < n ∧ j2 < k ∧
    cell f i0 j0 = true ∧ cell f i1 j1 = true ∧ cell f i2 j2 = false

/-- No 1 1 0 vertically, horizontally, diagonally or antidiagonally. -/
def good {n k : ℕ} (f : Fin n → Fin k → Bool) : Prop :=
  ∀ (i : Fin n) (j : Fin k),
    ¬ occurs f i j (i + 1) j (i + 2) j ∧ ¬ occurs f i j i (j + 1) i (j + 2) ∧
      ¬ occurs f i j (i + 1) (j + 1) (i + 2) (j + 2) ∧
      ¬ occurs f i (j + 2) (i + 1) (j + 1) (i + 2) j

instance {n k : ℕ} : DecidablePred (@good n k) := fun f => by
  unfold good occurs; infer_instance

/-- The number of good `n X 2` binary arrays. -/
def a (n : ℕ) : ℕ := (Finset.univ.filter (fun f : Fin n → Fin 2 → Bool => good f)).card

theorem main : ∀ n : ℕ, 1 ≤ n → a n = (Nat.fib (n + 3) - 1) ^ 2 := by
  sorry

end OMA.S_oeis_a188516

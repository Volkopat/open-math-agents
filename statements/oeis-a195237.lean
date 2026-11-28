import Mathlib

/-!
# A195237: Number of lower triangles of a 7 X 7 0..n array with each element differing from all of its diagonal, vertical, antidiagonal and horizontal neighbors by one or less.

Source: https://oeis.org/A195237
Credit: @ivillar

Status: open conjecture (Colin Barker, May 06 2018). The entry records, as conjectures:
* G.f.: x*(268435456 + 1126547401*x + 543337378*x^2 + 78250080*x^3 + 5176676*x^4 + 141128*x^5) / (1 - x)^2.
* a(n) = 2*a(n-1) - a(n-2) for n>6.
This file formalizes the second one, the recurrence, for every n > 6 exactly as stated.
(Robert Israel remarks in A195232, Nov 21 2017, that the entries of a solution differ by a
bounded amount, so the first differences are eventually constant; the recurrence on the full
range n > 6 is the claim made here.)

Formalization notes:
* Offset 1, as in the entry (data: 268435456, 1663418313, 3601738548, ...).
* The lower triangle of a 7 X 7 array is made of the cells `(i, j)` with column `j ≤` row `i`
  (`i, j ∈ {0, 1, ..., 6}`, row 0 on top, column 0 on the left), main diagonal included: its rows
  have 1, 2, ..., 7 cells, as in the examples of the entry (28 cells in all; a(1) = 2^28). An
  array is a map `f : Cell → Fin (n + 1)`, i.e. an entry in 0..n for each cell. Arrays are
  labelled: they are not identified up to symmetry.
* The diagonal, vertical, antidiagonal and horizontal neighbors of a cell are the other cells of
  the triangle whose row and column each differ from its own by at most 1 (the eight king
  directions, `Adj`). "Differing by one or less" means `|f p - f q| ≤ 1`. This is the same
  reading as in the statement of the sibling entry A195233 (row 3 of A195232).
* The recurrence is stated in `ℤ` for every n > 6, as in the entry.
-/

namespace OMA.S_oeis_a195237

/-- A cell of the lower triangle of a 7 X 7 array: the cell in row `p.1` and column `p.2`,
with `p.2 ≤ p.1`. -/
abbrev Cell := {p : Fin 7 × Fin 7 // p.2 ≤ p.1}

/-- Two cells are diagonal, vertical, antidiagonal or horizontal neighbors: they are distinct and
their rows, and their columns, differ by at most 1. -/
def Adj (p q : Fin 7 × Fin 7) : Prop :=
  p ≠ q ∧ |(p.1 : ℤ) - q.1| ≤ 1 ∧ |(p.2 : ℤ) - q.2| ≤ 1

/-- Each element of the lower triangle `f` differs from all of its neighbors by one or less. -/
def Good {n : ℕ} (f : Cell → Fin (n + 1)) : Prop :=
  ∀ p q : Cell, Adj p.1 q.1 → |(f p : ℤ) - f q| ≤ 1

/-- A195237(n): the number of lower triangles of a 7 X 7 array with entries in 0..n in which each
element differs from all of its neighbors by one or less. -/
noncomputable def a (n : ℕ) : ℕ := by
  classical
  exact Fintype.card {f : Cell → Fin (n + 1) // Good f}

/-- Barker's conjectured recurrence: `a(n) = 2a(n-1) - a(n-2)` for `n > 6`. -/
theorem main : ∀ n : ℕ, 6 < n → (a n : ℤ) = 2 * a (n - 1) - a (n - 2) := by
  sorry

end OMA.S_oeis_a195237

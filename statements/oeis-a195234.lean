import Mathlib

/-!
# A195234: Number of lower triangles of a 4 X 4 0..n array with each element differing from all of its diagonal, vertical, antidiagonal and horizontal neighbors by one or less.

Source: https://oeis.org/A195234
Credit: @ivillar

Status: open conjecture (Colin Barker, May 06 2018). The entry records, as conjectures:
* G.f.: x*(1024 + 1103*x + 150*x^2) / (1 - x)^2.
* a(n) = 2*a(n-1) - a(n-2) for n>3.
This file formalizes the second one, the recurrence, for every n > 3 exactly as stated.
(Robert Israel remarks in A195232, Nov 21 2017, that the entries of a solution differ by a
bounded amount, so the first differences are eventually constant; the recurrence on the full
range n > 3 is the claim made here.)

Formalization notes:
* Offset 1, as in the entry (data: 1024, 3151, 5428, 7705, 9982, ...).
* The lower triangle of a 4 X 4 array is made of the cells `(i, j)` with column `j ≤` row `i`
  (`i, j ∈ {0, 1, 2, 3}`, row 0 on top, column 0 on the left), main diagonal included: its rows
  have 1, 2, 3, 4 cells, as in the examples of the entry (10 cells in all; a(1) = 2^10). An
  array is a map `f : Cell → Fin (n + 1)`, i.e. an entry in 0..n for each cell. Arrays are
  labelled: they are not identified up to symmetry.
* The diagonal, vertical, antidiagonal and horizontal neighbors of a cell are the other cells of
  the triangle whose row and column each differ from its own by at most 1 (the eight king
  directions, `Adj`). "Differing by one or less" means `|f p - f q| ≤ 1`. This is the same
  reading as in the statement of the sibling entry A195233 (row 3 of A195232).
* The recurrence is stated in `ℤ` for every n > 3, as in the entry.
-/

namespace OMA.S_oeis_a195234

/-- A cell of the lower triangle of a 4 X 4 array: the cell in row `p.1` and column `p.2`,
with `p.2 ≤ p.1`. -/
abbrev Cell := {p : Fin 4 × Fin 4 // p.2 ≤ p.1}

/-- Two cells are diagonal, vertical, antidiagonal or horizontal neighbors: they are distinct and
their rows, and their columns, differ by at most 1. -/
def Adj (p q : Fin 4 × Fin 4) : Prop :=
  p ≠ q ∧ |(p.1 : ℤ) - q.1| ≤ 1 ∧ |(p.2 : ℤ) - q.2| ≤ 1

/-- Each element of the lower triangle `f` differs from all of its neighbors by one or less. -/
def Good {n : ℕ} (f : Cell → Fin (n + 1)) : Prop :=
  ∀ p q : Cell, Adj p.1 q.1 → |(f p : ℤ) - f q| ≤ 1

/-- A195234(n): the number of lower triangles of a 4 X 4 array with entries in 0..n in which each
element differs from all of its neighbors by one or less. -/
noncomputable def a (n : ℕ) : ℕ := by
  classical
  exact Fintype.card {f : Cell → Fin (n + 1) // Good f}

/-- Barker's conjectured recurrence: `a(n) = 2a(n-1) - a(n-2)` for `n > 3`. -/
theorem main : ∀ n : ℕ, 3 < n → (a n : ℤ) = 2 * a (n - 1) - a (n - 2) := by
  sorry

end OMA.S_oeis_a195234

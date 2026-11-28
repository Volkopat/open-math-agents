import Mathlib

/-!
# A195249: Number of lower triangles of a 3 X 3 0..n array with each element differing from all of its diagonal, vertical, antidiagonal and horizontal neighbors by two or less.

Source: https://oeis.org/A195249
Credit: @Salofe

Conjectures from Colin Barker, May 06 2018, quoted verbatim from the entry:
* "G.f.: x*(64 + 601*x + 288*x^2 + 94*x^3) / (1 - x)^2."
* "a(n) = 2*a(n-1) - a(n-2) for n>4."

Formalization notes:
* Offset 1, as in the entry (data: 64, 729, 1682, 2729, 3776, ...). The value `a 0` (entries in
  0..0) is never used.
* The lower triangle of a 3 X 3 array is made of the cells `(i, j)` with column `j ≤` row `i`
  (`i, j ∈ {0, 1, 2}`, row 0 on top, column 0 on the left), main diagonal included: its rows
  have 1, 2, 3 cells, as in the examples of the entry. An array is a map
  `f : Cell → Fin (n + 1)`, i.e. an entry in 0..n for each of the 6 cells. Arrays are labelled:
  they are not identified up to symmetry.
* The diagonal, vertical, antidiagonal and horizontal neighbors of a cell are the other cells of
  the triangle whose row and column each differ from its own by at most 1 (the eight king
  directions, `Adj`). "Differing by two or less" means `|f p - f q| ≤ 2`.
* This reading reproduces the data: exhaustive enumeration of all arrays gives 64, 729, 1682,
  2729, 3776 for n = 1, ..., 5 (and the listed terms up to n = 12), and the 10 solutions shown in
  the entry for n = 5 satisfy it. With horizontal and vertical neighbors only one would get 64,
  729, 2122 for n = 1, 2, 3. Counting instead the lower triangles of the valid full 3 X 3 arrays
  gives the same numbers: a valid triangle extends to a valid full array by giving the three cells
  above the diagonal the value of the center cell, which is a neighbor of every other cell of the
  triangle.
* The g.f. is the ordinary one, Sum_{n>=1} a(n) x^n, stated as an identity of formal power series
  over `ℚ` with the denominator `(1 - x)^2` cleared (it has constant coefficient 1, so it is
  invertible). The coefficient of x^0 is 0 since the sequence starts at n = 1.
* The recurrence is stated in `ℤ` for every n > 4, as in the entry (it fails at n = 4).
-/

namespace OMA.S_oeis_a195249

/-- A cell of the lower triangle of a 3 X 3 array: the cell in row `p.1` and column `p.2`,
with `p.2 ≤ p.1`. -/
abbrev Cell := {p : Fin 3 × Fin 3 // p.2 ≤ p.1}

/-- Two cells are diagonal, vertical, antidiagonal or horizontal neighbors: they are distinct and
their rows, and their columns, differ by at most 1. -/
def Adj (p q : Fin 3 × Fin 3) : Prop :=
  p ≠ q ∧ |(p.1 : ℤ) - q.1| ≤ 1 ∧ |(p.2 : ℤ) - q.2| ≤ 1

/-- Each element of the lower triangle `f` differs from all of its neighbors by two or less. -/
def Good {n : ℕ} (f : Cell → Fin (n + 1)) : Prop :=
  ∀ p q : Cell, Adj p.1 q.1 → |(f p : ℤ) - f q| ≤ 2

/-- A195249(n): the number of lower triangles of a 3 X 3 array with entries in 0..n in which each
element differs from all of its neighbors by two or less. -/
noncomputable def a (n : ℕ) : ℕ := by
  classical
  exact Fintype.card {f : Cell → Fin (n + 1) // Good f}

open PowerSeries in
/-- Barker's conjectures: the generating function `x(64 + 601x + 288x^2 + 94x^3)/(1 - x)^2`, and
the recurrence `a(n) = 2a(n-1) - a(n-2)` for `n > 4`. -/
theorem main :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) * (1 - X) ^ 2 =
        X * (64 + 601 * X + 288 * X ^ 2 + 94 * X ^ 3) ∧
    ∀ n : ℕ, 4 < n → (a n : ℤ) = 2 * a (n - 1) - a (n - 2) := by
  sorry

end OMA.S_oeis_a195249

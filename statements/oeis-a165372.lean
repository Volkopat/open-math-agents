import Mathlib

/-!
# A165372: Number of slanted n X 3 (i=1..n) X (j=i..3+i-1) 1..4 arrays with all 1s connected, all 2s connected, all 3s connected, all 4s connected, 1 in the upper left corner, 2 in the upper right corner, 3 in the lower left corner, and 4 in the lower right corner.

Source: https://oeis.org/A165372
Credit: @Salofe

OEIS Foundation and contributors, CC BY-SA 4.0. Retrieved 2026-11-27.

The conjectures, quoted verbatim from the FORMULA section of the entry:

  Conjectures from _Colin Barker_, Mar 25 2018: (Start)
  G.f.: x^2*(9 + 22*x + 33*x^2) / (1 - x)^2.
  a(n) = 8*(8*n-19) for n>2.
  (End)

Formalization notes:
* Offset 2, as in the entry (data: 9, 40, 104, 168, 232, 296, ...). The values `a 0` and
  `a 1` are never used.
* The slanted array has the rows i = 1..n, and row i has the three cells in the columns
  j = i..i+2. The cell `(i, k) : Fin n × Fin 3` is the cell in row i + 1 and column i + k + 1,
  so `k` is the position of the cell within its row (0 = leftmost).
* Connectedness refers to cells sharing an edge in the plane: two cells are neighbours when
  their absolute positions (row, column) differ by 1 in exactly one coordinate
  (`|Δrow| + |Δcolumn| = 1`, see `Adj`). So the cell in row i and column j has as neighbours
  those of (i, j - 1), (i, j + 1), (i - 1, j), (i + 1, j) that belong to the array.
* An array is a map `f : Fin n × Fin 3 → Fin 4`; the value `t` stands for the entry t + 1
  (0, 1, 2, 3 stand for 1, 2, 3, 4). Arrays are labelled: they are not identified up to
  symmetry.
* "All t's connected": any two cells holding t are joined by a path of neighbouring cells all
  holding t (`Relation.ReflTransGen` of the adjacency restricted to the cells holding t), i.e.
  the cells holding t induce a connected subgraph.
* The corners: upper left = row 1, column 1, i.e. `(0, 0)`; upper right = row 1, column 3,
  i.e. `(0, 2)`; lower left = row n, column n, i.e. `(n - 1, 0)`; lower right = row n,
  column n + 2, i.e. `(n - 1, 2)`. They hold 1, 2, 3, 4, i.e. `f` takes the values 0, 1, 2, 3
  there. This matches the examples of the entry (for n = 6 the first row of every example
  starts with 1 and ends with 2, the last row starts with 3 and ends with 4).
* The g.f. is the ordinary one, Sum_{n>=2} a(n) x^n, stated as an identity of formal power
  series over `ℚ` with the denominator `(1 - x)^2` cleared (it has constant coefficient 1, so
  it is invertible). The coefficients of x^0 and x^1 are 0 since the sequence starts at n = 2.
* The closed form is stated in `ℤ` for every n > 2, as in the entry.
-/

namespace OMA.S_oeis_a165372

/-- The cells `u` and `v` share an edge. The cell `(i, k)` lies in row `i` and column `i + k`
(counting from 0), and the two positions differ by 1 in exactly one coordinate. -/
def Adj {n : ℕ} (u v : Fin n × Fin 3) : Prop :=
  ((u.1 : ℤ) - v.1).natAbs + (((u.1 : ℤ) + u.2) - ((v.1 : ℤ) + v.2)).natAbs = 1

/-- All cells of the array `f` holding the value `c` are connected: any two of them are joined
by a path of neighbouring cells that all hold `c`. -/
def ClassConnected {n : ℕ} (f : Fin n × Fin 3 → Fin 4) (c : Fin 4) : Prop :=
  ∀ u v : Fin n × Fin 3, f u = c → f v = c →
    Relation.ReflTransGen (fun x y => Adj x y ∧ f x = c ∧ f y = c) u v

/-- The upper left, upper right, lower left and lower right corners hold 1, 2, 3, 4
(encoded as 0, 1, 2, 3). -/
def CornersOK {n : ℕ} (f : Fin n × Fin 3 → Fin 4) : Prop :=
  ∀ u : Fin n × Fin 3,
    ((u.1 : ℕ) = 0 → u.2 = 0 → f u = 0) ∧
    ((u.1 : ℕ) = 0 → u.2 = 2 → f u = 1) ∧
    ((u.1 : ℕ) = n - 1 → u.2 = 0 → f u = 2) ∧
    ((u.1 : ℕ) = n - 1 → u.2 = 2 → f u = 3)

/-- The arrays counted by A165372: every value class is connected and the corners hold
1, 2, 3, 4. -/
def IsCounted {n : ℕ} (f : Fin n × Fin 3 → Fin 4) : Prop :=
  (∀ c : Fin 4, ClassConnected f c) ∧ CornersOK f

/-- A165372(n): the number of slanted `n × 3` arrays with entries 1..4 as above. -/
noncomputable def a (n : ℕ) : ℕ := by
  classical
  exact Fintype.card {f : Fin n × Fin 3 → Fin 4 // IsCounted f}

open PowerSeries in
/-- Barker's conjectures: the generating function `x^2 (9 + 22x + 33x^2) / (1 - x)^2`, and
`a(n) = 8 (8n - 19)` for `n > 2`. -/
theorem main :
    PowerSeries.mk (fun n => if n < 2 then (0 : ℚ) else (a n : ℚ)) * (1 - X) ^ 2 =
        X ^ 2 * (9 + 22 * X + 33 * X ^ 2) ∧
    ∀ n : ℕ, 2 < n → (a n : ℤ) = 8 * (8 * n - 19) := by
  sorry

end OMA.S_oeis_a165372

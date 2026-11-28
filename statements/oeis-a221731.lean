import Mathlib

/-!
# A221731: Number of n X 2 arrays of occupancy after each element stays put or moves to some horizontal or antidiagonal neighbor, without move-in move-out left turns.

Source: https://oeis.org/A221731
Credit: @Salofe

The sequence is due to R. H. Hardin (Jan 22 2013); it is column 2 of A221736.

Conjectures from Colin Barker, Mar 14 2018, quoted verbatim from the entry:
* "G.f.: x*(3 + 2*x) / (1 - 5*x - 2*x^2)."
* "a(n) = (2^(-1-n)*((5-sqrt(33))^n*(-1+sqrt(33)) + (1+sqrt(33))*(5+sqrt(33))^n)) / sqrt(33)."

The entry also lists Hardin's "Empirical: a(n) = 5*a(n-1) + 2*a(n-2)."; that recurrence is not
part of this statement, which states Barker's two conjectures only.

Formalization notes:
* Offset 1, as in the entry (data: 3, 17, 91, 489, 2627, 14113, ...). The value `a 0` (it counts
  the empty array once) is never used: the g.f. has coefficient 0 at x^0, and the closed form is
  stated for n ≥ 1 only.
* The cells of an n X 2 array are the pairs `(i, j) : Fin n × Fin 2` (`Cell n`): `i` is the row
  (rows numbered from top to bottom) and `j` the column (columns numbered from left to right).
  Every cell holds one element. A choice of moves is a map `m : Cell n → Cell n`: the element of
  the cell `c` ends in the cell `m c`.
* Offsets are taken as integers, (row offset, column offset) = (`dr c d`, `dc c d`). The element
  of `c` stays put (`m c = c`), or moves to a horizontal neighbour of `c` (offset `(0, 1)` or
  `(0, -1)`, `IsHorizontalNbr`), or to an antidiagonal neighbour of `c` (offset `(-1, 1)`, up-right,
  or `(1, -1)`, down-left, `IsAntidiagonalNbr`). Only cells inside the array can be reached.
* A move-in move-out pair at a cell `d`: an element moves into `d` from a cell `c ≠ d`
  (`d = m c`), and the element of `d` moves out of `d` to `e = m d ≠ d`. It is a left turn when
  the step `d → e` turns counterclockwise relative to the step `c → d`, by an angle strictly
  between 0 and 180 degrees, as seen on the array printed with the first row at the top. With the
  column as x-coordinate and minus the row as y-coordinate, this is the condition that the cross
  product of the two steps is positive: `dr c d * dc d e - dc c d * dr d e > 0` (`LeftTurn`).
  Going straight on and turning back (two elements exchanging their cells) have cross product 0
  and are allowed. `Valid m` says that every move is allowed and that no move into a cell forms a
  left turn with the move out of that cell (every incoming element is checked).
* The occupancy array of `m` gives each cell `x` the number of elements that end in `x`,
  `occ m x = #{c | m c = x}`; `a n` is the number of distinct occupancy arrays `occ m` over all
  valid `m`. Arrays are labelled: they are not identified up to symmetry.
* This reading reproduces the data: enumerating the valid maps `m` with exactly these definitions
  gives 3, 17, 91, 489, 2627, 14113 for n = 1, ..., 6, and the same definitions for n X k arrays
  give the terms T(1, k) = 3, 8, 21, 55, 144 (k = 2..6), T(2, 3) = 152, T(2, 4) = 1347,
  T(2, 5) = 11917, T(3, 3) = 2904, T(3, 4) = 89920 and T(4, 3) = 54888 of the table A221736 (the
  45-degree left turns, such as a move to the right followed by a move up-right, occur only when
  there are at least 3 columns). Forbidding right turns instead (cross product negative) gives
  3, 15, 81, 435, ..., and forbidding only the 135-degree left turns gives T(2, 3) = 164.
* The g.f. is the ordinary one, Sum_{n>=1} a(n) x^n, stated as an identity of formal power series
  over `ℚ` with the denominator `1 - 5x - 2x^2` cleared (it has constant coefficient 1, so it is
  invertible). The coefficient of x^0 is 0 since the sequence starts at n = 1.
* The closed form is stated in `ℝ` for every n ≥ 1, with `2^(-1-n)` an integer power (`zpow`)
  and `sqrt` the real square root `Real.sqrt`.
-/

namespace OMA.S_oeis_a221731

/-- The cells of an n X 2 array: `(i, j)` is the cell in row `i` (rows numbered from top to
bottom) and column `j` (columns numbered from left to right). -/
abbrev Cell (n : ℕ) := Fin n × Fin 2

/-- The row offset from the cell `c` to the cell `d` (positive downwards). -/
def dr {n : ℕ} (c d : Cell n) : ℤ := (d.1 : ℤ) - c.1

/-- The column offset from the cell `c` to the cell `d` (positive to the right). -/
def dc {n : ℕ} (c d : Cell n) : ℤ := (d.2 : ℤ) - c.2

/-- `d` is a horizontal neighbour of `c`: the offset from `c` to `d` is `(0, 1)` or `(0, -1)`. -/
def IsHorizontalNbr {n : ℕ} (c d : Cell n) : Prop :=
  dr c d = 0 ∧ (dc c d = 1 ∨ dc c d = -1)

/-- `d` is an antidiagonal neighbour of `c`: the offset from `c` to `d` is `(-1, 1)` (up-right)
or `(1, -1)` (down-left). -/
def IsAntidiagonalNbr {n : ℕ} (c d : Cell n) : Prop :=
  (dr c d = -1 ∧ dc c d = 1) ∨ (dr c d = 1 ∧ dc c d = -1)

/-- The step `d → e` turns left (counterclockwise, as seen on the printed array) relative to the
step `c → d`: in the coordinates (column, minus row) the cross product of the two steps is
positive. -/
def LeftTurn {n : ℕ} (c d e : Cell n) : Prop :=
  0 < dr c d * dc d e - dc c d * dr d e

/-- Every element stays put or moves to a horizontal or antidiagonal neighbour, and there is no
move-in move-out left turn: whenever an element moves from `c` into the cell `m c` and the
element of `m c` moves out of it to `m (m c)`, the turn `c → m c → m (m c)` is not a left turn. -/
def Valid {n : ℕ} (m : Cell n → Cell n) : Prop :=
  (∀ c, m c = c ∨ IsHorizontalNbr c (m c) ∨ IsAntidiagonalNbr c (m c)) ∧
  (∀ c, m c ≠ c → m (m c) ≠ m c → ¬ LeftTurn c (m c) (m (m c)))

/-- The occupancy array of `m`: the number of elements that end in the cell `x`. -/
def occ {n : ℕ} (m : Cell n → Cell n) (x : Cell n) : ℕ :=
  (Finset.univ.filter (fun c => m c = x)).card

/-- A221731(n): the number of distinct occupancy arrays `occ m`, over all valid choices of moves
`m` on the n X 2 array. -/
noncomputable def a (n : ℕ) : ℕ := by
  classical
  exact ((Finset.univ.filter (fun m : Cell n → Cell n => Valid m)).image occ).card

open PowerSeries in
/-- Barker's conjectures: the generating function `x(3 + 2x)/(1 - 5x - 2x^2)`, and the closed form
`a(n) = 2^(-1-n) ((5 - √33)^n (-1 + √33) + (1 + √33) (5 + √33)^n) / √33` for `n ≥ 1`. -/
theorem main :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) * (1 - 5 * X - 2 * X ^ 2) =
        X * (3 + 2 * X) ∧
    (∀ n : ℕ, 1 ≤ n → (a n : ℝ) =
      (2 : ℝ) ^ (-1 - (n : ℤ)) * ((5 - Real.sqrt 33) ^ n * (-1 + Real.sqrt 33) +
        (1 + Real.sqrt 33) * (5 + Real.sqrt 33) ^ n) / Real.sqrt 33) := by
  sorry

end OMA.S_oeis_a221731

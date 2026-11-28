import Mathlib

/-!
# A220932: Equals two maps: number of n X 3 binary arrays indicating the locations of corresponding elements equal to exactly two of their horizontal and antidiagonal neighbors in a random 0..2 n X 3 array.

Source: https://oeis.org/A220932
Credit: @Salofe

The sequence is due to R. H. Hardin (Dec 25 2012); it is column 3 of A220935.

Conjectures from Colin Barker, Mar 13 2018, quoted verbatim from the entry:
* "G.f.: 2*x*(1 + 3*x) / ((1 + x)*(1 - 6*x))."
* "a(n) = (2^n*3^(n+1) + 4) / 7 for n even."
* "a(n) = (2^n*3^(n+1) - 4) / 7 for n odd"

The entry also lists Hardin's "Empirical: a(n) = 5*a(n-1) + 6*a(n-2)."; that recurrence is not
part of this statement, which states Barker's three conjectures only.

Formalization notes:
* Offset 1, as in the entry (data: 2, 16, 92, 556, 3332, 19996, ...). The value `a 0` (it counts
  the empty array once) is never used: the g.f. has coefficient 0 at x^0, and both closed forms
  are stated for n ≥ 1 only.
* An n X 3 0..2 array is a function `A : Fin n → Fin 3 → Fin 3`; `A i j` is the entry in row `i`
  (rows numbered from top to bottom) and column `j` (columns numbered from left to right). An
  n X 3 binary array is a function `Fin n → Fin 3 → Bool` (`true` stands for 1). Arrays are
  labelled: they are not identified up to symmetry.
* Neighbours: the cell `(i', j')` is a neighbour of the cell `(i, j)` when the offset
  `(i' - i, j' - j)` is `(0, 1)` or `(0, -1)` (its horizontal neighbours), or `(-1, 1)` or
  `(1, -1)` (its antidiagonal neighbours, up-right and down-left); only cells inside the array
  count (`IsNbr`). A cell is not its own neighbour.
* The binary array of `A` has a 1 at `(i, j)` exactly when the element `A i j` is equal to
  exactly two of these neighbours, i.e. exactly two neighbours `q` of `(i, j)` have
  `A q = A i j` (`eqTwo`).
* `a n` is the number of distinct binary arrays `fun i j => eqTwo A (i, j)`, over all n X 3
  arrays `A` with entries in 0..2 (the "random" array ranges over all of them).
* Reading the antidiagonal neighbours as the diagonal ones, the offsets `(-1, -1)` and `(1, 1)`,
  gives the same numbers: reversing the order of the columns (`j ↦ 2 - j`) is a bijection on the
  arrays `A`, it exchanges the two diagonal directions, keeps the horizontal neighbours, and
  reverses the columns of the binary arrays.
* This reading reproduces the data: an exhaustive enumeration of all 0..2 n X 3 arrays, computing
  exactly the definitions below, gives 2, 16, 92, 556 for n = 1, ..., 4; an automaton count of
  the same definition gives all 210 terms of the b-file (n = 1..210); and the same definition
  for n X k arrays reproduces all 30 terms T(n, k) with n k ≤ 12 listed in the table A220935
  (for instance 1, 4, 12, 37, 114, 351 for n X 2, and 1, 1, 2, 4, 7, 12, 21, 37, 65, 114 for
  1 X k). Taking the vertical neighbours `(1, 0)`, `(-1, 0)` instead of the antidiagonal ones
  would give 2, 23, 236, 2095 for n = 1, ..., 4 instead.
* The g.f. is the ordinary one, Sum_{n>=1} a(n) x^n, stated as an identity of formal power series
  over `ℚ` with the denominator `(1 + x)(1 - 6x)` cleared (it has constant coefficient 1, so it
  is invertible). The coefficient of x^0 is 0 since the sequence starts at n = 1.
* The two closed forms are stated in `ℚ`, where `/ 7` is exact division, for every even,
  respectively odd, n ≥ 1.
-/

namespace OMA.S_oeis_a220932

/-- The cell `q` is a horizontal or antidiagonal neighbour of the cell `p`: the offset from `p`
to `q` (row offset, column offset) is `(0, 1)`, `(0, -1)`, `(-1, 1)` or `(1, -1)`. -/
def IsNbr {n : ℕ} (p q : Fin n × Fin 3) : Prop :=
  ((q.1 : ℤ) - p.1, (q.2 : ℤ) - p.2) ∈ ({(0, 1), (0, -1), (-1, 1), (1, -1)} : Finset (ℤ × ℤ))

/-- The element of `A` at the cell `p` is equal to exactly two of its horizontal and
antidiagonal neighbours inside the array. -/
noncomputable def eqTwo {n : ℕ} (A : Fin n → Fin 3 → Fin 3) (p : Fin n × Fin 3) : Bool := by
  classical
  exact decide ((Finset.univ.filter (fun q => IsNbr p q ∧ A q.1 q.2 = A p.1 p.2)).card = 2)

/-- A220932(n): the number of distinct n X 3 binary arrays `fun i j => eqTwo A (i, j)`, over all
n X 3 arrays `A` with entries in 0..2. -/
noncomputable def a (n : ℕ) : ℕ := by
  classical
  exact (Finset.univ.image (fun A : Fin n → Fin 3 → Fin 3 => fun i j => eqTwo A (i, j))).card

open PowerSeries in
/-- Barker's conjectures: the generating function `2x(1 + 3x)/((1 + x)(1 - 6x))`, and
`a(n) = (2^n 3^(n+1) + 4)/7` for even `n`, `a(n) = (2^n 3^(n+1) - 4)/7` for odd `n`. -/
theorem main :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) * ((1 + X) * (1 - 6 * X)) =
        2 * X * (1 + 3 * X) ∧
    (∀ n : ℕ, 1 ≤ n → Even n → (a n : ℚ) = (2 ^ n * 3 ^ (n + 1) + 4) / 7) ∧
    (∀ n : ℕ, 1 ≤ n → Odd n → (a n : ℚ) = (2 ^ n * 3 ^ (n + 1) - 4) / 7) := by
  sorry

end OMA.S_oeis_a220932

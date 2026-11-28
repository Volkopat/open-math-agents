import Mathlib

/-!
# A219810: Number of n X 2 arrays of the minimum value of corresponding elements and their horizontal, vertical or diagonal neighbors in a random, but sorted with lexicographically nondecreasing rows and nonincreasing columns, 0..2 n X 2 array.

Source: https://oeis.org/A219810
Credit: @Salofe

The sequence is due to R. H. Hardin (Nov 28 2012); it is column 2 of A219816.

Conjectures from the entry, quoted verbatim:
* R. H. Hardin, in the entry he created (Nov 28 2012): "Empirical: a(n) = (1/12)*n^4 -
  (1/2)*n^3 + (41/12)*n^2 - 3*n + 1 for n>1."
* Colin Barker, Jul 28 2018: "G.f.: x*(3 - 9*x + 16*x^2 - 17*x^3 + 11*x^4 - 2*x^5) /
  (1 - x)^5." and "a(n) = 5*a(n-1) - 10*a(n-2) + 10*a(n-3) - 5*a(n-4) + a(n-5) for n>6."

Formalization notes:
* Offset 1, as in the entry (data: 3, 6, 16, 33, 61, 106, 176, ...). The value `a 0` (it counts
  the empty array once) is never used: Hardin's formula is stated for n > 1, the g.f. has
  coefficient 0 at x^0, and the recurrence (n > 6) only involves a(n-5), ..., a(n) with
  n - 5 ≥ 2.
* An n X 2 0..2 array is a function `A : Fin n → Fin 2 → Fin 3`; `A i j` is the entry in row `i`
  (rows numbered from top to bottom) and column `j` (columns numbered from left to right), with
  the usual order 0 < 1 < 2 on entries. Arrays are labelled: they are not identified up to
  symmetry.
* "Sorted with lexicographically nondecreasing rows and nonincreasing columns": the rows, each
  read left to right, are lexicographically nondecreasing from top to bottom,
  `Monotone (fun i => toLex (A i))`, and the columns, each read top to bottom, are
  lexicographically nonincreasing from left to right,
  `Antitone (fun j => toLex (fun i => A i j))`. `toLex` gives the words Mathlib's order
  `Pi.Lex`, in which the first position where two words differ decides.
* Neighbours: the cell `(i', j')` is taken into account at the cell `(i, j)` when the offset
  `(i' - i, j' - j)` is `(0, 0)` (the element itself), `(0, 1)` or `(0, -1)` (its horizontal
  neighbours), `(1, 0)` or `(-1, 0)` (its vertical neighbours), or `(1, 1)` or `(-1, -1)` (its
  diagonal neighbours: one row down and one column right, or one row up and one column left;
  in Hardin's families of these sequences the other two offsets `(1, -1)` and `(-1, 1)` are the
  antidiagonal neighbours, which are not used here); only cells inside the array count
  (`IsNbr`). The resulting array has at `(i, j)` the minimum of the entries of `A` at these
  cells (`minNbr`; the set always contains `(i, j)` itself, so the infimum is this minimum).
* `a n` is the number of distinct resulting arrays, over all sorted n X 2 0..2 arrays `A` (the
  "random" array ranges over all sorted arrays).
* This reading reproduces the data: an exhaustive enumeration of all 0..2 n X 2 arrays,
  computing exactly the definitions below, gives 3, 6, 16, 33, 61, 106, 176 for n = 1, ..., 7;
  an automaton count of the same definition gives all 210 terms of the b-file (n = 1..210); all
  ten 3 X 2 arrays shown in the entry are obtained; and the same definition for n X 1 and n X 3
  arrays gives 3, 3, 6, 10, 15, 21, 28 and 6, 15, 62, 169, columns 1 and 3 of A219816 (for
  1 X k and 2 X k arrays it gives 3, 3, 6, 10, 15 and 3, 6, 15, 28, 45, its rows 1 and 2).
  Reading the diagonal neighbours as the antidiagonal ones, offsets `(1, -1)` and `(-1, 1)`,
  would give 3, 4, 9, 19, 35 for n = 1..5 instead, and reading the columns as
  lexicographically nondecreasing would give 3, 3, 11, 25, 48.
* Hardin's formula is stated in `ℚ` for every n > 1, as in the entry (it fails at n = 1, where
  it gives 1 while a(1) = 3).
* The g.f. is the ordinary one, Sum_{n>=1} a(n) x^n, stated as an identity of formal power series
  over `ℚ` with the denominator `(1 - x)^5` cleared (it has constant coefficient 1, so it is
  invertible). The coefficient of x^0 is 0 since the sequence starts at n = 1.
* The recurrence is stated in `ℤ` for every n > 6, as in the entry (it fails at n = 6).
-/

namespace OMA.S_oeis_a219810

/-- The rows of `A`, read left to right, are lexicographically nondecreasing from top to bottom,
and the columns of `A`, read top to bottom, are lexicographically nonincreasing from left to
right. -/
def Sorted {n : ℕ} (A : Fin n → Fin 2 → Fin 3) : Prop :=
  Monotone (fun i => toLex (A i)) ∧ Antitone (fun j => toLex (fun i => A i j))

/-- The cell `q` is the cell `p` itself or one of its horizontal, vertical or diagonal
neighbours: the offset from `p` to `q` (row offset, column offset) is `(0, 0)`, `(0, 1)`,
`(0, -1)`, `(1, 0)`, `(-1, 0)`, `(1, 1)` or `(-1, -1)`. -/
def IsNbr {n : ℕ} (p q : Fin n × Fin 2) : Prop :=
  ((q.1 : ℤ) - p.1, (q.2 : ℤ) - p.2) ∈
    ({(0, 0), (0, 1), (0, -1), (1, 0), (-1, 0), (1, 1), (-1, -1)} : Finset (ℤ × ℤ))

/-- The minimum of the entries of `A` at the cell `p` and at its horizontal, vertical and
diagonal neighbours inside the array. -/
noncomputable def minNbr {n : ℕ} (A : Fin n → Fin 2 → Fin 3) (p : Fin n × Fin 2) : Fin 3 := by
  classical
  exact (Finset.univ.filter (fun q => IsNbr p q)).inf (fun q => A q.1 q.2)

/-- A219810(n): the number of distinct n X 2 arrays `fun i j => minNbr A (i, j)` of minimum
values, over all sorted n X 2 arrays `A` with entries in 0..2. -/
noncomputable def a (n : ℕ) : ℕ := by
  classical
  exact ((Finset.univ.filter (fun A : Fin n → Fin 2 → Fin 3 => Sorted A)).image
    (fun A => fun i j => minNbr A (i, j))).card

open PowerSeries in
/-- Hardin's formula `a(n) = n^4/12 - n^3/2 + 41 n^2/12 - 3 n + 1` for `n > 1`, Barker's
generating function `x(3 - 9x + 16x^2 - 17x^3 + 11x^4 - 2x^5)/(1 - x)^5`, and Barker's
recurrence `a(n) = 5a(n-1) - 10a(n-2) + 10a(n-3) - 5a(n-4) + a(n-5)` for `n > 6`. -/
theorem main :
    (∀ n : ℕ, 1 < n →
      (a n : ℚ) = (1 / 12) * (n : ℚ) ^ 4 - (1 / 2) * (n : ℚ) ^ 3 + (41 / 12) * (n : ℚ) ^ 2
        - 3 * (n : ℚ) + 1) ∧
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) * (1 - X) ^ 5 =
        X * (3 - 9 * X + 16 * X ^ 2 - 17 * X ^ 3 + 11 * X ^ 4 - 2 * X ^ 5) ∧
    (∀ n : ℕ, 6 < n → (a n : ℤ) = 5 * a (n - 1) - 10 * a (n - 2) + 10 * a (n - 3) -
      5 * a (n - 4) + a (n - 5)) := by
  sorry

end OMA.S_oeis_a219810

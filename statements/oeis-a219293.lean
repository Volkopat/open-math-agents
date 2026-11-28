import Mathlib

/-!
# A219293: Number of n X 2 arrays of the minimum value of corresponding elements and their horizontal, vertical or antidiagonal neighbors in a random, but sorted with lexicographically nondecreasing rows and columns, 0..2 n X 2 array.

Source: https://oeis.org/A219293
Credit: @Salofe

The sequence is due to R. H. Hardin (Nov 17 2012); it is column 2 of A219299.

Conjectures from Colin Barker, Jul 25 2018, quoted verbatim from the entry:
* "G.f.: x*(3 - 8*x + 12*x^2 - 10*x^3 + 2*x^4 + 5*x^5 - 2*x^6) / (1 - x)^5."
* "a(n) = 5*a(n-1) - 10*a(n-2) + 10*a(n-3) - 5*a(n-4) + a(n-5) for n > 7."

The entry also lists Hardin's "Empirical: a(n) = (1/12)*n^4 - (2/3)*n^3 + (53/12)*n^2 -
(17/6)*n - 3 for n > 2."; that closed form is not part of this statement, which states Barker's
two conjectures only.

Formalization notes:
* Offset 1, as in the entry (data: 3, 7, 17, 35, 62, 103, 165, 257, 390, ...). The value `a 0`
  (it counts the empty array once) is never used: the g.f. has coefficient 0 at x^0, and the
  recurrence (n > 7) only involves a(n-5), ..., a(n) with n - 5 ≥ 3.
* An n X 2 0..2 array is a function `A : Fin n → Fin 2 → Fin 3`; `A i j` is the entry in row `i`
  (rows numbered from top to bottom) and column `j` (columns numbered from left to right), with
  the usual order 0 < 1 < 2 on entries. Arrays are labelled: they are not identified up to
  symmetry.
* "Sorted with lexicographically nondecreasing rows and columns": the rows, each read left to
  right, are lexicographically nondecreasing from top to bottom,
  `Monotone (fun i => toLex (A i))`, and the columns, each read top to bottom, are
  lexicographically nondecreasing from left to right, `Monotone (fun j => toLex (fun i => A i j))`.
  `toLex` gives the words Mathlib's order `Pi.Lex`, in which the first position where two words
  differ decides.
* Neighbours: the cell `(i', j')` is taken into account at the cell `(i, j)` when the offset
  `(i' - i, j' - j)` is `(0, 0)` (the element itself), `(0, 1)` or `(0, -1)` (its horizontal
  neighbours), `(1, 0)` or `(-1, 0)` (its vertical neighbours), or `(-1, 1)` or `(1, -1)` (its
  antidiagonal neighbours, up-right and down-left); only cells inside the array count (`IsNbr`).
  The resulting array has at `(i, j)` the minimum of the entries of `A` at these cells
  (`minNbr`; the set always contains `(i, j)` itself, so the infimum is this minimum).
* `a n` is the number of distinct resulting arrays, over all sorted n X 2 0..2 arrays `A`.
* This reading reproduces the data: exhaustive enumeration gives 3, 7, 17, 35, 62, 103, 165,
  257, 390, 577, 833 for n = 1, ..., 11; an automaton count of the same definition gives all
  210 terms of the b-file (n = 1..210); and the same definition for n X 3 and n X 1 arrays gives
  6, 17, 77, 261, 800, 2361 and 3, 3, 6, 10, 15, 21, 28, columns 3 and 1 of A219299. Taking the
  diagonal neighbours `(-1, -1)`, `(1, 1)` instead of the antidiagonal ones would give 3, 3, 11,
  25, ... instead.
* The g.f. is the ordinary one, Sum_{n>=1} a(n) x^n, stated as an identity of formal power series
  over `ℚ` with the denominator `(1 - x)^5` cleared (it has constant coefficient 1, so it is
  invertible). The coefficient of x^0 is 0 since the sequence starts at n = 1.
* The recurrence is stated in `ℤ` for every n > 7, as in the entry.
-/

namespace OMA.S_oeis_a219293

/-- The rows of `A`, read left to right, are lexicographically nondecreasing from top to bottom,
and the columns of `A`, read top to bottom, are lexicographically nondecreasing from left to
right. -/
def Sorted {n : ℕ} (A : Fin n → Fin 2 → Fin 3) : Prop :=
  Monotone (fun i => toLex (A i)) ∧ Monotone (fun j => toLex (fun i => A i j))

/-- The cell `q` is the cell `p` itself or one of its horizontal, vertical or antidiagonal
neighbours: the offset from `p` to `q` (row offset, column offset) is `(0, 0)`, `(0, 1)`,
`(0, -1)`, `(1, 0)`, `(-1, 0)`, `(-1, 1)` or `(1, -1)`. -/
def IsNbr {n : ℕ} (p q : Fin n × Fin 2) : Prop :=
  ((q.1 : ℤ) - p.1, (q.2 : ℤ) - p.2) ∈
    ({(0, 0), (0, 1), (0, -1), (1, 0), (-1, 0), (-1, 1), (1, -1)} : Finset (ℤ × ℤ))

/-- The minimum of the entries of `A` at the cell `p` and at its horizontal, vertical and
antidiagonal neighbours inside the array. -/
noncomputable def minNbr {n : ℕ} (A : Fin n → Fin 2 → Fin 3) (p : Fin n × Fin 2) : Fin 3 := by
  classical
  exact (Finset.univ.filter (fun q => IsNbr p q)).inf (fun q => A q.1 q.2)

/-- A219293(n): the number of distinct n X 2 arrays `fun i j => minNbr A (i, j)` of minimum
values, over all sorted n X 2 arrays `A` with entries in 0..2. -/
noncomputable def a (n : ℕ) : ℕ := by
  classical
  exact ((Finset.univ.filter (fun A : Fin n → Fin 2 → Fin 3 => Sorted A)).image
    (fun A => fun i j => minNbr A (i, j))).card

open PowerSeries in
/-- Barker's conjectures: the generating function
`x(3 - 8x + 12x^2 - 10x^3 + 2x^4 + 5x^5 - 2x^6)/(1 - x)^5`, and the recurrence
`a(n) = 5a(n-1) - 10a(n-2) + 10a(n-3) - 5a(n-4) + a(n-5)` for `n > 7`. -/
theorem main :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) * (1 - X) ^ 5 =
        X * (3 - 8 * X + 12 * X ^ 2 - 10 * X ^ 3 + 2 * X ^ 4 + 5 * X ^ 5 - 2 * X ^ 6) ∧
    (∀ n : ℕ, 7 < n → (a n : ℤ) = 5 * a (n - 1) - 10 * a (n - 2) + 10 * a (n - 3) -
      5 * a (n - 4) + a (n - 5)) := by
  sorry

end OMA.S_oeis_a219293

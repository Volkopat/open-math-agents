import Mathlib

/-!
# A220198: Number of n X 2 arrays of the minimum value of corresponding elements and their horizontal, vertical or diagonal neighbors in a random, but sorted with lexicographically nondecreasing rows and nonincreasing columns, 0..3 n X 2 array.

Source: https://oeis.org/A220198
Credit: @Salofe

The sequence is due to R. H. Hardin (Dec 07 2012); it is column 2 of A220204.

Conjectures from the entry, quoted verbatim:
* R. H. Hardin, in the entry he created (Dec 07 2012): "Empirical: a(n) = (1/20160)*n^8 -
  (1/5040)*n^7 - (1/480)*n^6 + (107/720)*n^5 - (1151/960)*n^4 + (278/45)*n^3 -
  (54427/5040)*n^2 + (5323/420)*n - 7 for n>1."
* Colin Barker, Jul 30 2018: "G.f.: x*(4 - 26*x + 92*x^2 - 215*x^3 + 350*x^4 - 386*x^5 +
  277*x^6 - 119*x^7 + 29*x^8 - 4*x^9) / (1 - x)^9." and "a(n) = 9*a(n-1) - 36*a(n-2) +
  84*a(n-3) - 126*a(n-4) + 126*a(n-5) - 84*a(n-6) + 36*a(n-7) - 9*a(n-8) + a(n-9) for n>10."

Formalization notes:
* Offset 1, as in the entry (data: 4, 10, 38, 103, 245, 547, 1168, ...). The value `a 0` (it
  counts the empty array once) is never used: Hardin's formula is stated for n > 1, the g.f. has
  coefficient 0 at x^0, and the recurrence (n > 10) only involves a(n-9), ..., a(n) with
  n - 9 ≥ 2.
* An n X 2 0..3 array is a function `A : Fin n → Fin 2 → Fin 4`; `A i j` is the entry in row `i`
  (rows numbered from top to bottom) and column `j` (columns numbered from left to right), with
  the usual order 0 < 1 < 2 < 3 on entries. Arrays are labelled: they are not identified up to
  symmetry.
* "Sorted with lexicographically nondecreasing rows and nonincreasing columns": the rows, each
  read left to right, are lexicographically nondecreasing from top to bottom,
  `Monotone (fun i => toLex (A i))`, and the columns, each read top to bottom, are
  lexicographically nonincreasing from left to right,
  `Antitone (fun j => toLex (fun i => A i j))`. `toLex` gives the words Mathlib's order
  `Pi.Lex`, in which the first position where two words differ decides.
* Neighbours: the cell `(i', j')` is taken into account at the cell `(i, j)` when the offset
  `(i' - i, j' - j)` is `(0, 0)` (the element itself), `(0, 1)` or `(0, -1)` (its horizontal
  neighbours), `(1, 0)` or `(-1, 0)` (its vertical neighbours), or `(-1, -1)` or `(1, 1)` (its
  diagonal neighbours: the cells up-left and down-right of it, on the same diagonal, which runs
  from the top left towards the bottom right); only cells inside the array count (`IsNbr`). The
  resulting array has at `(i, j)` the minimum of the entries of `A` at these cells (`minNbr`;
  the set always contains `(i, j)` itself, so the infimum is this minimum).
* `a n` is the number of distinct resulting arrays, over all sorted n X 2 0..3 arrays `A` (the
  "random" array ranges over all sorted arrays).
* This reading reproduces the data: an exhaustive enumeration of all 0..3 n X 2 arrays,
  computing exactly the definitions below, gives 4, 10, 38, 103, 245 for n = 1, ..., 5, and an
  enumeration of the sorted arrays gives 547, 1168, 2395 for n = 6, 7, 8; an automaton count of
  the same definition gives all 210 terms of the b-file (n = 1..210); all ten 3 X 2 arrays
  shown in the entry are obtained; and the same definition for n X 1 and n X 3 arrays gives
  4, 4, 10, 20, 35, 56, 84, 120, 165 and 10, 36, 238, 1013, 3916, columns 1 and 3 of A220204
  (for 3 X 4 arrays it gives 956, and all five 3 X 4 arrays shown in A220204). The other
  readings do not match: with both diagonal directions (adding `(-1, 1)` and `(1, -1)`) one gets
  4, 4, 13, 26, 57 for n = 1..5, with the antidiagonal neighbours `(-1, 1)`, `(1, -1)` instead
  of the diagonal ones 4, 7, 20, 58, 141, and reading the columns as lexicographically
  nondecreasing 4, 4, 23, 70, 173.
* Hardin's formula is stated in `ℚ` for every n > 1, as in the entry (it fails at n = 1, where
  it gives 0 while a(1) = 4).
* The g.f. is the ordinary one, Sum_{n>=1} a(n) x^n, stated as an identity of formal power series
  over `ℚ` with the denominator `(1 - x)^9` cleared (it has constant coefficient 1, so it is
  invertible). The coefficient of x^0 is 0 since the sequence starts at n = 1.
* The recurrence is stated in `ℤ` for every n > 10, as in the entry (it fails at n = 10, where
  the right side is 8986 while a(10) = 8982).
-/

namespace OMA.S_oeis_a220198

/-- The rows of `A`, read left to right, are lexicographically nondecreasing from top to bottom,
and the columns of `A`, read top to bottom, are lexicographically nonincreasing from left to
right. -/
def Sorted {n : ℕ} (A : Fin n → Fin 2 → Fin 4) : Prop :=
  Monotone (fun i => toLex (A i)) ∧ Antitone (fun j => toLex (fun i => A i j))

/-- The cell `q` is the cell `p` itself or one of its horizontal, vertical or diagonal
neighbours: the offset from `p` to `q` (row offset, column offset) is `(0, 0)`, `(0, 1)`,
`(0, -1)`, `(1, 0)`, `(-1, 0)`, `(-1, -1)` or `(1, 1)`. -/
def IsNbr {n : ℕ} (p q : Fin n × Fin 2) : Prop :=
  ((q.1 : ℤ) - p.1, (q.2 : ℤ) - p.2) ∈
    ({(0, 0), (0, 1), (0, -1), (1, 0), (-1, 0), (-1, -1), (1, 1)} : Finset (ℤ × ℤ))

/-- The minimum of the entries of `A` at the cell `p` and at its horizontal, vertical and
diagonal neighbours inside the array. -/
noncomputable def minNbr {n : ℕ} (A : Fin n → Fin 2 → Fin 4) (p : Fin n × Fin 2) : Fin 4 := by
  classical
  exact (Finset.univ.filter (fun q => IsNbr p q)).inf (fun q => A q.1 q.2)

/-- A220198(n): the number of distinct n X 2 arrays `fun i j => minNbr A (i, j)` of minimum
values, over all sorted n X 2 arrays `A` with entries in 0..3. -/
noncomputable def a (n : ℕ) : ℕ := by
  classical
  exact ((Finset.univ.filter (fun A : Fin n → Fin 2 → Fin 4 => Sorted A)).image
    (fun A => fun i j => minNbr A (i, j))).card

open PowerSeries in
/-- Hardin's formula `a(n) = n^8/20160 - n^7/5040 - n^6/480 + 107 n^5/720 - 1151 n^4/960 +
278 n^3/45 - 54427 n^2/5040 + 5323 n/420 - 7` for `n > 1`, Barker's generating function
`x(4 - 26x + 92x^2 - 215x^3 + 350x^4 - 386x^5 + 277x^6 - 119x^7 + 29x^8 - 4x^9)/(1 - x)^9`,
and Barker's recurrence `a(n) = 9a(n-1) - 36a(n-2) + 84a(n-3) - 126a(n-4) + 126a(n-5) -
84a(n-6) + 36a(n-7) - 9a(n-8) + a(n-9)` for `n > 10`. -/
theorem main :
    (∀ n : ℕ, 1 < n →
      (a n : ℚ) = (1 / 20160) * (n : ℚ) ^ 8 - (1 / 5040) * (n : ℚ) ^ 7 - (1 / 480) * (n : ℚ) ^ 6
        + (107 / 720) * (n : ℚ) ^ 5 - (1151 / 960) * (n : ℚ) ^ 4 + (278 / 45) * (n : ℚ) ^ 3
        - (54427 / 5040) * (n : ℚ) ^ 2 + (5323 / 420) * (n : ℚ) - 7) ∧
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) * (1 - X) ^ 9 =
        X * (4 - 26 * X + 92 * X ^ 2 - 215 * X ^ 3 + 350 * X ^ 4 - 386 * X ^ 5 + 277 * X ^ 6
          - 119 * X ^ 7 + 29 * X ^ 8 - 4 * X ^ 9) ∧
    (∀ n : ℕ, 10 < n → (a n : ℤ) = 9 * a (n - 1) - 36 * a (n - 2) + 84 * a (n - 3) -
      126 * a (n - 4) + 126 * a (n - 5) - 84 * a (n - 6) + 36 * a (n - 7) - 9 * a (n - 8) +
      a (n - 9)) := by
  sorry

end OMA.S_oeis_a220198

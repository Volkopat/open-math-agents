import Mathlib

/-!
# A220033: Number of 3 X n arrays of the minimum value of corresponding elements and their horizontal or diagonal neighbors in a random, but sorted with lexicographically nondecreasing rows and nonincreasing columns, 0..1 3 X n array.

Source: https://oeis.org/A220033
Credit: @Salofe

Conjectures from the entry, quoted verbatim:
* R. H. Hardin, in the entry he created (Dec 03 2012):
  "Empirical: a(n) = (1/2)*n^2 + (13/2)*n - 15 for n>3."
* Colin Barker, Jul 30 2018:
  "G.f.: x*(4 - 6*x + 4*x^2 + 3*x^3 - 3*x^4 - x^5) / (1 - x)^3." and
  "a(n) = 3*a(n-1) - 3*a(n-2) + a(n-3) for n>6."

Formalization notes:
* Offset 1, as in the entry (data: 4, 6, 10, 19, 30, 42, 55, ...). The value `a 0` (the empty
  array, counted once) is never used: every claim below is about n ≥ 1 only.
* A 3 X n 0..1 array is a function `A : Fin 3 → Fin n → Fin 2`; `A i j` is the entry in row `i`
  (top to bottom) and column `j` (left to right), with the order 0 < 1 on entries. Arrays are
  labelled: they are not identified up to symmetry.
* "Sorted with lexicographically nondecreasing rows and nonincreasing columns" means that the
  rows, each read left to right as a word, are in lexicographically nondecreasing order from top
  to bottom, `Monotone (fun i => toLex (A i))`, and that the columns, each read top to bottom as
  a word, are in lexicographically nonincreasing order from left to right,
  `Antitone (fun j => toLex (fun i => A i j))`. Here `toLex` gives `Fin k → Fin 2` Mathlib's
  lexicographic order `Pi.Lex`, in which the first differing position decides (the leftmost
  entry of a row, the top entry of a column).
* "The minimum value of corresponding elements and their horizontal or diagonal neighbors": the
  entry at `(i, j)` of the new array is the minimum of `A i j` and of the entries of `A` at those
  of the cells `(i, j - 1)`, `(i, j + 1)` (horizontal neighbours), `(i - 1, j - 1)` and
  `(i + 1, j + 1)` (diagonal neighbours) that lie inside the array (a cell on the border has
  fewer neighbours; nothing wraps around). In R. H. Hardin's array sequences "diagonal" and
  "antidiagonal" are different directions (the same family has sequences with "horizontal or
  antidiagonal neighbors", e.g. A219714): "diagonal" is the direction of the main diagonal,
  upper left to lower right, so the antidiagonal cells `(i - 1, j + 1)` and `(i + 1, j - 1)`
  are not neighbours here. The minimum is written as the infimum `Finset.inf` in `Fin 2` over
  this set of cells (`Near i j`); the set always contains `(i, j)` itself, so the infimum is the
  minimum of the listed entries.
* `a n` counts the distinct 3 X n arrays obtained this way from some sorted 0..1 3 X n array
  (the "random" array ranges over all sorted arrays).
* This reading matches the entry: an exhaustive enumeration of all 0..1 3 X n arrays, computing
  exactly the definitions below, reproduces the data for n ≤ 7, an enumeration over the arrays
  with sorted columns reproduces it for n ≤ 20, and all seven 3 X 3 arrays shown in the entry
  are obtained. The same definitions with R rows instead of 3 reproduce the table A220032 (whose
  row 3 is this sequence) for every R X k with R * k ≤ 21, including the five 3 X 4 arrays
  shown there. Reading "diagonal" as the antidiagonal, or as both diagonals, gives 3 instead of
  4 for the 2 X 2 arrays of A220032 and misses arrays shown in the entry.
* Hardin's formula is stated in `ℚ` for every n > 3, as in the entry.
* The g.f. is the ordinary one, Sum_{n>=1} a(n) x^n, stated as an identity of formal power
  series over `ℚ` with the denominator `(1 - x)^3` cleared (it has constant coefficient 1, so it
  is invertible). The coefficient of x^0 is 0 since the sequence starts at n = 1.
* Barker's recurrence is stated in `ℤ` for every n > 6, as in the entry.
-/

namespace OMA.S_oeis_a220033

/-- The rows of `A`, read left to right, are in lexicographically nondecreasing order from top
to bottom, and the columns of `A`, read top to bottom, are in lexicographically nonincreasing
order from left to right. -/
def Sorted {n : ℕ} (A : Fin 3 → Fin n → Fin 2) : Prop :=
  Monotone (fun i => toLex (A i)) ∧ Antitone (fun j => toLex (fun i => A i j))

/-- The cell `p` is the cell `(i, j)` itself, one of its horizontal neighbours `(i, j ± 1)`, or
one of its diagonal neighbours `(i - 1, j - 1)` and `(i + 1, j + 1)`. -/
def Near {n : ℕ} (i : Fin 3) (j : Fin n) (p : Fin 3 × Fin n) : Prop :=
  (p.1 = i ∧ p.2 = j) ∨
    (p.1 = i ∧ (p.2.val + 1 = j.val ∨ j.val + 1 = p.2.val)) ∨
    ((p.1.val + 1 = i.val ∧ p.2.val + 1 = j.val) ∨ (i.val + 1 = p.1.val ∧ j.val + 1 = p.2.val))

/-- The minimum of the entry of `A` at `(i, j)` and of the entries of `A` at the horizontal and
diagonal neighbours of `(i, j)` inside the array. -/
noncomputable def nbhdMin {n : ℕ} (A : Fin 3 → Fin n → Fin 2) (i : Fin 3) (j : Fin n) :
    Fin 2 := by
  classical
  exact (Finset.univ.filter (fun p : Fin 3 × Fin n => Near i j p)).inf (fun p => A p.1 p.2)

/-- A220033(n): the number of 3 X n arrays `B` such that, for some sorted 0..1 3 X n array `A`,
every entry `B i j` is the minimum of `A i j` and its horizontal and diagonal neighbours in
`A`. -/
noncomputable def a (n : ℕ) : ℕ := by
  classical
  exact Fintype.card
    {B : Fin 3 → Fin n → Fin 2 // ∃ A : Fin 3 → Fin n → Fin 2, Sorted A ∧ nbhdMin A = B}

open PowerSeries in
/-- Hardin's formula, Barker's g.f. and Barker's recurrence. -/
theorem main :
    (∀ n : ℕ, 3 < n →
      (a n : ℚ) = (1 / 2) * (n : ℚ) ^ 2 + (13 / 2) * (n : ℚ) - 15) ∧
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) * (1 - X) ^ 3 =
        X * (4 - 6 * X + 4 * X ^ 2 + 3 * X ^ 3 - 3 * X ^ 4 - X ^ 5) ∧
    (∀ n : ℕ, 6 < n →
      (a n : ℤ) = 3 * a (n - 1) - 3 * a (n - 2) + a (n - 3)) := by
  sorry

end OMA.S_oeis_a220033

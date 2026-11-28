import Mathlib

/-!
# A219498: Number of n X 4 arrays of the minimum value of corresponding elements and their horizontal or vertical neighbors in a random, but sorted with lexicographically nondecreasing rows and nonincreasing columns, 0..1 n X 4 array.

Source: https://oeis.org/A219498
Credit: @Salofe

Conjectures from the entry, quoted verbatim:
* R. H. Hardin, in the entry he created (Nov 20 2012): "Empirical: a(n) = (1/6)*n^3 + 1*n^2
  + (23/6)*n - 7 for n>2."
* Colin Barker, Jul 26 2018: "G.f.: x*(4 - 9*x + 14*x^2 - 11*x^3 + 2*x^4 + x^5) / (1 - x)^4."
  and "a(n) = 4*a(n-1) - 6*a(n-2) + 4*a(n-3) - a(n-4) for n>6."

Formalization notes:
* Offset 1, as in the entry (data: 4, 7, 18, 35, 58, 88, ...). The value `a 0` (the empty
  array, counted once) is never used: every claim below is about n ≥ 1 only.
* An n X 4 0..1 array is a function `A : Fin n → Fin 4 → Fin 2`; `A i j` is the entry in row `i`
  (top to bottom) and column `j` (left to right), with the order 0 < 1 on entries. Arrays are
  labelled: they are not identified up to symmetry.
* "Sorted with lexicographically nondecreasing rows and nonincreasing columns" means that the
  rows, each read left to right as a word, are in lexicographically nondecreasing order from top
  to bottom, `Monotone (fun i => toLex (A i))`, and that the columns, each read top to bottom as
  a word, are in lexicographically nonincreasing order from left to right,
  `Antitone (fun j => toLex (fun i => A i j))`. Here `toLex` gives `Fin k → Fin 2` Mathlib's
  lexicographic order `Pi.Lex`, in which the first differing position decides (the leftmost
  entry of a row, the top entry of a column).
* "The minimum value of corresponding elements and their horizontal or vertical neighbors": the
  entry at `(i, j)` of the new array is the minimum of `A i j` and of the entries of `A` at those
  of the cells `(i, j - 1)`, `(i, j + 1)`, `(i - 1, j)`, `(i + 1, j)` that lie inside the array
  (a cell on the border has fewer neighbours; nothing wraps around). It is written as the
  infimum `Finset.inf` in `Fin 2` over this set of cells (`Near i j`); the set always contains
  `(i, j)` itself, so the infimum is the minimum of the listed entries.
* `a n` counts the distinct n X 4 arrays obtained this way from some sorted 0..1 n X 4 array
  (the "random" array ranges over all sorted arrays).
* This reading matches the entry: an exhaustive enumeration of all 0..1 n X 4 arrays, computing
  exactly the definitions below, reproduces the data for n ≤ 4, an enumeration over the arrays
  with sorted rows reproduces it for n ≤ 8, and all five 3 X 4 arrays shown in the entry are
  obtained. Reading the columns as lexicographically nondecreasing instead gives
  4, 9, 42, 149 for n = 1..4.
* Hardin's formula is stated in `ℚ` for every n > 2, as in the entry.
* The g.f. is the ordinary one, Sum_{n>=1} a(n) x^n, stated as an identity of formal power
  series over `ℚ` with the denominator `(1 - x)^4` cleared (it has constant coefficient 1, so it
  is invertible). The coefficient of x^0 is 0 since the sequence starts at n = 1.
* Barker's recurrence is stated in `ℤ` for every n > 6, as in the entry.
-/

namespace OMA.S_oeis_a219498

/-- The rows of `A`, read left to right, are in lexicographically nondecreasing order from top
to bottom, and the columns of `A`, read top to bottom, are in lexicographically nonincreasing
order from left to right. -/
def Sorted {n : ℕ} (A : Fin n → Fin 4 → Fin 2) : Prop :=
  Monotone (fun i => toLex (A i)) ∧ Antitone (fun j => toLex (fun i => A i j))

/-- The cell `p` is the cell `(i, j)` itself or one of its horizontal or vertical neighbours. -/
def Near {n : ℕ} (i : Fin n) (j : Fin 4) (p : Fin n × Fin 4) : Prop :=
  (p.1 = i ∧ p.2 = j) ∨
    (p.1 = i ∧ (p.2.val + 1 = j.val ∨ j.val + 1 = p.2.val)) ∨
    (p.2 = j ∧ (p.1.val + 1 = i.val ∨ i.val + 1 = p.1.val))

/-- The minimum of the entry of `A` at `(i, j)` and of the entries of `A` at the horizontal and
vertical neighbours of `(i, j)` inside the array. -/
noncomputable def nbhdMin {n : ℕ} (A : Fin n → Fin 4 → Fin 2) (i : Fin n) (j : Fin 4) :
    Fin 2 := by
  classical
  exact (Finset.univ.filter (fun p : Fin n × Fin 4 => Near i j p)).inf (fun p => A p.1 p.2)

/-- A219498(n): the number of n X 4 arrays `B` such that, for some sorted 0..1 n X 4 array `A`,
every entry `B i j` is the minimum of `A i j` and its horizontal and vertical neighbours in `A`. -/
noncomputable def a (n : ℕ) : ℕ := by
  classical
  exact Fintype.card
    {B : Fin n → Fin 4 → Fin 2 // ∃ A : Fin n → Fin 4 → Fin 2, Sorted A ∧ nbhdMin A = B}

open PowerSeries in
/-- Hardin's formula, Barker's g.f. and Barker's recurrence. -/
theorem main :
    (∀ n : ℕ, 2 < n →
      (a n : ℚ) = (1 / 6) * (n : ℚ) ^ 3 + 1 * (n : ℚ) ^ 2 + (23 / 6) * (n : ℚ) - 7) ∧
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) * (1 - X) ^ 4 =
        X * (4 - 9 * X + 14 * X ^ 2 - 11 * X ^ 3 + 2 * X ^ 4 + X ^ 5) ∧
    (∀ n : ℕ, 6 < n →
      (a n : ℤ) = 4 * a (n - 1) - 6 * a (n - 2) + 4 * a (n - 3) - a (n - 4)) := by
  sorry

end OMA.S_oeis_a219498

import Mathlib

/-!
# A184130: Number of n X 2 0..2 arrays with rows and columns in nondecreasing order.

Source: https://oeis.org/A184130
Credit: @Salofe

Conjectures from the entry, quoted verbatim:
* Colin Barker, Apr 12 2018: "G.f.: x*(2 - x)*(3 - 11*x + 28*x^2 - 42*x^3 + 39*x^4 - 22*x^5
  + 7*x^6 - x^7) / (1 - x)^9." and "a(n) = (40320 + 79344*n + 64140*n^2 + 37884*n^3
  + 16009*n^4 + 3696*n^5 + 490*n^6 + 36*n^7 + n^8) / 40320."
* R. H. Hardin, in the entry he created (Jan 09 2011): "Empirical: a(n) = 9*a(n-1) - 36*a(n-2)
  + 84*a(n-3) - 126*a(n-4) + 126*a(n-5) - 84*a(n-6) + 36*a(n-7) - 9*a(n-8) + a(n-9)
  (=polynomial of degree 8)."

Formalization notes:
* Offset 1, as in the entry (data: 6, 29, 112, 356, 972, ...). The value `a 0` (the empty
  array, counted once) is never used: every claim below is about n ≥ 1 only.
* An n X 2 0..2 array is a function `A : Fin n → Fin 2 → Fin 3`; `A i j` is the entry in row `i`
  (top to bottom) and column `j` (left to right), with the usual order 0 < 1 < 2 on entries.
  Arrays are labelled: they are not identified up to symmetry.
* "Rows in nondecreasing order" means that the rows, each read left to right as a word, are in
  lexicographically nondecreasing order from top to bottom: `Monotone (fun i => toLex (A i))`.
  "Columns in nondecreasing order" means that the columns, each read top to bottom as a word,
  are in lexicographically nondecreasing order from left to right:
  `Monotone (fun j => toLex (fun i => A i j))`. Here `toLex` gives `Fin k → Fin 3` Mathlib's
  lexicographic order `Pi.Lex`, in which the first differing position decides (the leftmost
  entry of a row, the top entry of a column).
* This lexicographic reading is the one that matches the entry: it reproduces the data (checked
  by exhaustive enumeration for n ≤ 15), and all ten 3 X 2 solutions shown in the entry satisfy
  it, e.g. the array with rows `1 2`, `2 0`, `2 1`, whose second column `2, 0, 1` is not itself
  a nondecreasing sequence. The other reading, where every row and every column is a
  nondecreasing sequence of entries, gives a(2) = 20 instead of 29.
* The closed form is stated in `ℚ` (the division by 40320 is exact) for every n ≥ 1.
* The g.f. is the ordinary one, Sum_{n>=1} a(n) x^n, stated as an identity of formal power
  series over `ℚ` with the denominator `(1 - x)^9` cleared (it has constant coefficient 1, so it
  is invertible). The coefficient of x^0 is 0 since the sequence starts at n = 1.
* Hardin's recurrence is stated in `ℤ` for every n > 9, the indices for which a(n-9) is a term
  of the sequence (offset 1). His remark "(=polynomial of degree 8)" is stated as: some
  polynomial `P` over `ℚ` of degree 8 satisfies P(n) = a(n) for every n ≥ 1.
-/

namespace OMA.S_oeis_a184130

/-- The rows of `A`, read left to right, are in lexicographically nondecreasing order from top
to bottom, and the columns of `A`, read top to bottom, are in lexicographically nondecreasing
order from left to right. -/
def RowsColsSorted {n : ℕ} (A : Fin n → Fin 2 → Fin 3) : Prop :=
  Monotone (fun i => toLex (A i)) ∧ Monotone (fun j => toLex (fun i => A i j))

/-- A184130(n): the number of n X 2 arrays with entries in {0, 1, 2} whose rows and columns
are in nondecreasing order. -/
noncomputable def a (n : ℕ) : ℕ := by
  classical
  exact Fintype.card {A : Fin n → Fin 2 → Fin 3 // RowsColsSorted A}

open PowerSeries in
/-- Barker's closed form and g.f., and Hardin's recurrence with its remark that a(n) is a
polynomial of degree 8 in n. -/
theorem main :
    (∀ n : ℕ, 1 ≤ n → (a n : ℚ) = (40320 + 79344 * (n : ℚ) + 64140 * (n : ℚ) ^ 2
        + 37884 * (n : ℚ) ^ 3 + 16009 * (n : ℚ) ^ 4 + 3696 * (n : ℚ) ^ 5 + 490 * (n : ℚ) ^ 6
        + 36 * (n : ℚ) ^ 7 + (n : ℚ) ^ 8) / 40320) ∧
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) * (1 - X) ^ 9 =
        X * (2 - X) * (3 - 11 * X + 28 * X ^ 2 - 42 * X ^ 3 + 39 * X ^ 4 - 22 * X ^ 5
          + 7 * X ^ 6 - X ^ 7) ∧
    (∀ n : ℕ, 9 < n → (a n : ℤ) = 9 * a (n - 1) - 36 * a (n - 2) + 84 * a (n - 3)
        - 126 * a (n - 4) + 126 * a (n - 5) - 84 * a (n - 6) + 36 * a (n - 7) - 9 * a (n - 8)
        + a (n - 9)) ∧
    (∃ P : Polynomial ℚ, P.natDegree = 8 ∧ ∀ n : ℕ, 1 ≤ n → P.eval (n : ℚ) = (a n : ℚ)) := by
  sorry

end OMA.S_oeis_a184130

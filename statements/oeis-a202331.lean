import Mathlib

/-!
# A202331: Number of (n+1) X 5 binary arrays with consecutive windows of two bits considered as a binary number nondecreasing in every row and column.

Source: https://oeis.org/A202331
Credit: @Salofe

Conjectures from Colin Barker, May 27 2018, quoted verbatim from the entry (sequence by
R. H. Hardin, Dec 17 2011):
"Conjectures from Colin Barker, May 27 2018: (Start)
G.f.: x*(49 - 165*x + 250*x^2 - 203*x^3 + 86*x^4 - 15*x^5) / (1 - x)^6.
a(n) = 6*a(n-1) - 15*a(n-2) + 20*a(n-3) - 15*a(n-4) + 6*a(n-5) - a(n-6) for n>6.
(End)"

Formalization notes:
* Offset 1, as in the entry (data: 49, 129, 289, 576, 1052, 1796, ...): `a n` counts the arrays
  with `n + 1` rows and 5 columns.
* An (n+1) X 5 binary array is a function `A : Fin (n + 1) → Fin 5 → Fin 2`; `A i j` is the
  entry in row `i` (top to bottom) and column `j` (left to right). Arrays are labelled: they are
  not identified up to symmetry.
* Each row is read left to right and each column top to bottom, as a word `v : Fin L → Fin 2`
  (`L = 5` for a row, `L = n + 1` for a column). Its consecutive (overlapping) windows of two
  bits are the pairs `(v i, v (i + 1))` for `i + 1 < L`. The window starting at `i`, considered
  as a binary number with its first bit as the most significant one, is
  `window v i = 2 * v i + v (i + 1)`, a value in {0, 1, 2, 3}.
* "Nondecreasing" means that each window is at most the next one:
  `window v i ≤ window v (i + 1)` whenever `i + 2 < L` (equivalently, the sequence of windows is
  monotone). A word with at most two bits has at most one window, and the condition is empty.
* This reading reproduces the data: exhaustive enumeration of all arrays gives 49, 129, 289 for
  n = 1, 2, 3; enumeration of the arrays whose rows satisfy the condition gives 49, 129, 289,
  576, 1052, 1796, 2906 for n = 1, ..., 7; a transfer-matrix count derived from it agrees with
  the whole b-file (n = 1, ..., 210); and the four 6 X 5 solutions shown in the entry satisfy
  it. Reading each window with its first bit as the least significant one gives the same
  counts, but it rejects three of the four example solutions (for instance their row 0 0 0 1 0);
  reading the rows right to left, or the columns bottom to top, rejects all four.
* The g.f. is the ordinary one, Sum_{n>=1} a(n) x^n, stated as an identity of formal power
  series over `ℤ` with the denominator `(1 - x)^6` cleared (its constant coefficient is 1, so it
  is invertible and clearing it is an equivalence). The definition also makes sense for n = 0,
  outside the range of the entry (1 X 5 arrays); the coefficient of x^0 of the series is set to
  0, matching the g.f. sum over n >= 1.
* The recurrence is stated in `ℤ` for every n > 6, as in the entry (all indices are then >= 1).
* The entry also lists R. H. Hardin's empirical formula a(n) = (1/60)*n^5 + (3/8)*n^4 + 3*n^3
  + (89/8)*n^2 + (1169/60)*n + 15; it is not part of Barker's conjectures and is not stated
  here.
-/

namespace OMA.S_oeis_a202331

/-- The window of two consecutive bits of the word `v` starting at position `i`, that is the pair
`(v i, v (i + 1))`, considered as a binary number with its first bit as the most significant one:
`2 * v i + v (i + 1)`. -/
def window {L : ℕ} (v : Fin L → Fin 2) (i : ℕ) (hi : i + 1 < L) : ℕ :=
  2 * (v ⟨i, by omega⟩).val + (v ⟨i + 1, hi⟩).val

/-- The consecutive windows of two bits of the word `v`, considered as binary numbers, are
nondecreasing: each window is at most the next one. -/
def WindowsNondecreasing {L : ℕ} (v : Fin L → Fin 2) : Prop :=
  ∀ (i : ℕ) (hi : i + 2 < L), window v i (by omega) ≤ window v (i + 1) hi

/-- The array `A` (whose row `i`, column `j` entry is `A i j`) has nondecreasing windows in every
row, read left to right, and in every column, read top to bottom. -/
def IsValid {n : ℕ} (A : Fin (n + 1) → Fin 5 → Fin 2) : Prop :=
  (∀ i, WindowsNondecreasing (A i)) ∧ (∀ j, WindowsNondecreasing (fun i => A i j))

/-- A202331(n): the number of (n+1) X 5 binary arrays whose consecutive windows of two bits,
considered as binary numbers, are nondecreasing in every row and every column. -/
noncomputable def a (n : ℕ) : ℕ := by
  classical
  exact Fintype.card {A : Fin (n + 1) → Fin 5 → Fin 2 // IsValid A}

open PowerSeries in
/-- Barker's conjectures: the g.f. `x(49 - 165x + 250x^2 - 203x^3 + 86x^4 - 15x^5)/(1 - x)^6`
of `Sum_{n ≥ 1} a(n) x^n`, and the recurrence
`a(n) = 6a(n-1) - 15a(n-2) + 20a(n-3) - 15a(n-4) + 6a(n-5) - a(n-6)` for `n > 6`. -/
theorem main :
    (PowerSeries.mk (fun n => if n = 0 then (0 : ℤ) else (a n : ℤ)) * (1 - X) ^ 6 =
        X * (49 - 165 * X + 250 * X ^ 2 - 203 * X ^ 3 + 86 * X ^ 4 - 15 * X ^ 5)) ∧
    ∀ n : ℕ, n > 6 →
      (a n : ℤ) = 6 * a (n - 1) - 15 * a (n - 2) + 20 * a (n - 3) - 15 * a (n - 4) +
        6 * a (n - 5) - a (n - 6) := by
  sorry

end OMA.S_oeis_a202331

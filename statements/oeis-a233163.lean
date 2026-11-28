import Mathlib

/-!
# A233163: Number of n X 3 0..7 arrays with no element x(i,j) adjacent to itself or value 7-x(i,j) horizontally, diagonally, antidiagonally or vertically, top left element zero, and 1 appearing before 2 3 4 5 and 6, 2 appearing before 3 4 and 5, and 3 appearing before 4 in row major order (unlabelled 8-colorings with no clashing color pairs).

Source: https://oeis.org/A233163
Credit: @Salofe

The sequence is due to R. H. Hardin (Dec 05 2013); it is column 3 of A233168.

Conjectures from Colin Barker, Oct 09 2018, quoted verbatim from the entry:
* "G.f.: x*(3 - 64*x + 288*x^2) / ((1 - 8*x)*(1 - 16*x))."
* "a(n) = 8^(n-2) * (2^n+4) for n>1."

The entry also lists Hardin's "Empirical: a(n) = 24*a(n-1) - 128*a(n-2) for n>3."; that
recurrence is not part of this statement, which states Barker's two conjectures only.

Formalization notes:
* Offset 1, as in the entry (data: 3, 8, 96, 1280, 18432, 278528, 4325376, ...). The value `a 0`
  is never used: the g.f. has coefficient 0 at x^0, and the closed form is claimed for n > 1
  only. (With the definitions below `a 0 = 1`, the empty array.)
* An n X 3 0..7 array is a function `A : Fin n → Fin 3 → Fin 8`; `A i j` is the element x(i,j)
  in row `i` (rows numbered from the top) and column `j` (columns numbered from the left).
  Arrays are labelled: they are not identified up to any symmetry (the normalization "top left
  element zero" and the three "appearing before" conditions are part of the definition).
* Adjacency (`Adj`): two distinct cells are adjacent horizontally, vertically, diagonally or
  antidiagonally exactly when their row indices differ by at most one and their column indices
  differ by at most one (the eight king neighbours; the array does not wrap around).
* "No element x(i,j) adjacent to itself or value 7-x(i,j)": for all adjacent cells `(i, j)` and
  `(i', j')`, x(i',j') ≠ x(i,j) and x(i',j') ≠ 7 - x(i,j) (the subtraction is in `ℕ` and exact,
  since elements are at most 7). Equivalently, adjacent elements lie in different classes of the
  clashing colour pairs {0,7}, {1,6}, {2,5}, {3,4}.
* "Top left element zero": x(0,0) = 0 (required for n ≥ 1; for n = 0 there is no such element).
* Row major order numbers the cell `(i, j)` as `pos i j = 3 i + j`. "v appearing before S"
  (`AppearsBefore A v S`) means: every cell whose element lies in `S` is preceded in row major
  order by some cell with element `v`. Equivalently, for each value `w` of `S` that occurs in the
  array, the value `v` occurs as well and its first occurrence comes before the first occurrence
  of `w`; a value of `S` that does not occur imposes nothing. The three conditions are
  `AppearsBefore A 1 {2, 3, 4, 5, 6}`, `AppearsBefore A 2 {3, 4, 5}` and
  `AppearsBefore A 3 {4}`.
* This reading reproduces the data: an exhaustive enumeration of all n X 3 arrays over 0..7 for
  n = 1, 2, and a pruned exhaustive search for n = 3, 4, 5, computing exactly the definitions
  below, give 3, 8, 96, 1280, 18432; the seven 5 X 3 example arrays shown in the entry all
  satisfy `Good`. (The looser reading in which a condition is checked only when both values
  occur would also allow the row 0, 2, 0 and give a(1) > 3.)
* The g.f. is the ordinary one, Sum_{n>=1} a(n) x^n, stated as an identity of formal power series
  over `ℚ` with the denominator `(1 - 8x)(1 - 16x)` cleared (it has constant coefficient 1, so it
  is invertible). The coefficient of x^0 is 0 since the sequence starts at n = 1.
* The closed form is stated in `ℕ` for every n > 1, as in the entry (`n - 2` is then exact).
-/

namespace OMA.S_oeis_a233163

open PowerSeries

/-- The cells `(i, j)` and `(i', j')` (row, column) are adjacent horizontally, vertically,
diagonally or antidiagonally: they are distinct, and their rows and their columns each differ by
at most one. -/
def Adj (i j i' j' : ℕ) : Prop :=
  (i, j) ≠ (i', j') ∧ i ≤ i' + 1 ∧ i' ≤ i + 1 ∧ j ≤ j' + 1 ∧ j' ≤ j + 1

/-- The position of the cell `(i, j)` (row `i`, column `j`) of an n X 3 array in row major
order. -/
def pos (i j : ℕ) : ℕ := 3 * i + j

/-- In the n X 3 array `A`, the value `v` appears before every value of `S` in row major order:
each cell whose element lies in `S` comes after some cell with element `v`. -/
def AppearsBefore {n : ℕ} (A : Fin n → Fin 3 → Fin 8) (v : Fin 8) (S : Finset (Fin 8)) :
    Prop :=
  ∀ (i : Fin n) (j : Fin 3), A i j ∈ S →
    ∃ (i' : Fin n) (j' : Fin 3), pos i' j' < pos i j ∧ A i' j' = v

/-- The n X 3 array `A` over 0..7 is counted by A233163: no element is adjacent (horizontally,
diagonally, antidiagonally or vertically) to itself or to 7 minus itself, the top left element
is zero, and in row major order 1 appears before 2, 3, 4, 5 and 6, 2 appears before 3, 4 and 5,
and 3 appears before 4. -/
def Good {n : ℕ} (A : Fin n → Fin 3 → Fin 8) : Prop :=
  (∀ (i i' : Fin n) (j j' : Fin 3), Adj i j i' j' →
      A i' j' ≠ A i j ∧ (A i' j' : ℕ) ≠ 7 - (A i j : ℕ)) ∧
    (∀ h : 0 < n, A ⟨0, h⟩ 0 = 0) ∧
    AppearsBefore A 1 {2, 3, 4, 5, 6} ∧ AppearsBefore A 2 {3, 4, 5} ∧ AppearsBefore A 3 {4}

/-- A233163(n): the number of n X 3 0..7 arrays satisfying `Good`. -/
noncomputable def a (n : ℕ) : ℕ := Nat.card {A : Fin n → Fin 3 → Fin 8 // Good A}

/-- Barker's conjectures: the generating function
`x(3 - 64x + 288x^2)/((1 - 8x)(1 - 16x))`, and `a(n) = 8^(n-2) (2^n + 4)` for `n > 1`. -/
theorem main :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) *
        ((1 - 8 * X) * (1 - 16 * X)) = X * (3 - 64 * X + 288 * X ^ 2) ∧
    (∀ n : ℕ, 1 < n → a n = 8 ^ (n - 2) * (2 ^ n + 4)) := by
  sorry

end OMA.S_oeis_a233163

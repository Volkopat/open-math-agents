import Mathlib

/-!
# OEIS A253503: Barker's generating function and recurrence

Source: https://oeis.org/A253503 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry (R. H. Hardin, Jan 02 2015), offset 1: Number of (n+2) X (1+2) 0..1 arrays with every 2 X 2
and 3 X 3 subblock diagonal maximum minus antidiagonal minimum nondecreasing horizontally and
vertically. Data: 132, 260, 428, 636, 884, ... The formula section states: Empirical: a(n) = 20*n^2
+ 68*n + 44. Conjectures from _Colin Barker_, Dec 16 2018: (Start) G.f.: 4*x*(33 - 34*x + 11*x^2) /
(1 - x)^3. a(n) = 3*a(n-1) - 3*a(n-2) + a(n-3) for n>3. (End)

Formalization notes:
* An (n+2) X 3 array over 0..1 is a function `Fin (n + 2) → Fin 3 → Fin 2`, x i j being the element
  in row i and column j, both counted from 0; `get` reads it as an integer (0 outside, which no
  condition reaches).
* The diagonal of the s X s subblock with upper left element (i, j) is (i, j), (i+1, j+1), ..., and
  its antidiagonal is (i, j+s-1), (i+1, j+s-2), ..., (i+s-1, j); `f2` and `f3` give the diagonal
  maximum minus the antidiagonal minimum for s = 2 and s = 3.
* Nondecreasing horizontally and vertically: for each size, the value of a subblock is at most the
  value of the subblock of the same size one column to its right and of the one one row below,
  whenever that subblock lies inside the array (`good`). With 3 columns there are two 2 X 2
  subblocks and one 3 X 3 subblock in each band of rows.
* `a n` is `Set.ncard` of the set of these arrays, a set of functions between finite types.
* The g.f. is A(x) = Sum_{n >= 1} a(n) x^n (offset 1; the count for n = 0 is not a term of the
  sequence and is replaced by 0), stated as A(x) (1 - x)^3 = 4x (33 - 34x + 11x^2) in Z[[x]], which
  is equivalent because (1 - x)^3 has constant term 1. The recurrence is stated in the integers for
  n > 3, as in the entry.
* `main` is the conjunction of Barker's two conjectures.
* Controls proved in the proof file: a(1..14), all the entry's listed terms.
-/

namespace OMA.S_oeis_a253503

open PowerSeries

/-- The element of the R X 3 array x in row r and column c, both counted from 0, as an integer, or 0
outside the array (the conditions below read only elements inside). -/
def get (R : ℕ) (x : Fin R → Fin 3 → Fin 2) (r c : ℕ) : ℤ :=
  if h : r < R ∧ c < 3 then ((x ⟨r, h.1⟩ ⟨c, h.2⟩).val : ℤ) else 0

/-- The diagonal maximum minus the antidiagonal minimum of the 2 X 2 subblock with upper left element
(i, j): the diagonal is (i, j), (i+1, j+1) and the antidiagonal (i, j+1), (i+1, j). -/
def f2 (R : ℕ) (x : Fin R → Fin 3 → Fin 2) (i j : ℕ) : ℤ :=
  max (get R x i j) (get R x (i + 1) (j + 1)) - min (get R x i (j + 1)) (get R x (i + 1) j)

/-- The diagonal maximum minus the antidiagonal minimum of the 3 X 3 subblock with upper left element
(i, j): the diagonal is (i, j), (i+1, j+1), (i+2, j+2) and the antidiagonal (i, j+2), (i+1, j+1),
(i+2, j). -/
def f3 (R : ℕ) (x : Fin R → Fin 3 → Fin 2) (i j : ℕ) : ℤ :=
  max (max (get R x i j) (get R x (i + 1) (j + 1))) (get R x (i + 2) (j + 2)) -
    min (min (get R x i (j + 2)) (get R x (i + 1) (j + 1))) (get R x (i + 2) j)

/-- The values of the 2 X 2 subblocks and those of the 3 X 3 subblocks are nondecreasing horizontally
and vertically: the value of each subblock is at most that of the subblock of the same size one
column to its right and that of the subblock one row below, when that subblock lies inside the
array. -/
def good (R : ℕ) (x : Fin R → Fin 3 → Fin 2) : Prop :=
  (∀ i j : ℕ, i + 2 ≤ R → j + 2 ≤ 3 →
      (j + 3 ≤ 3 → f2 R x i j ≤ f2 R x i (j + 1)) ∧ (i + 3 ≤ R → f2 R x i j ≤ f2 R x (i + 1) j)) ∧
    (∀ i j : ℕ, i + 3 ≤ R → j + 3 ≤ 3 →
      (j + 4 ≤ 3 → f3 R x i j ≤ f3 R x i (j + 1)) ∧ (i + 4 ≤ R → f3 R x i j ≤ f3 R x (i + 1) j))

/-- A253503(n): the number of (n+2) X 3 arrays over 0..1 with every 2 X 2 and 3 X 3 subblock diagonal
maximum minus antidiagonal minimum nondecreasing horizontally and vertically. -/
noncomputable def a (n : ℕ) : ℕ := Set.ncard {x : Fin (n + 2) → Fin 3 → Fin 2 | good (n + 2) x}

/-- Barker's conjectures: the g.f. and the recurrence. -/
theorem main :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℤ) else a n) * (1 - X) ^ 3 = 4 * X * (33 - 34 * X + 11 * X ^ 2) ∧
    ∀ n : ℕ, 3 < n → (a n : ℤ) = 3 * a (n - 1) - 3 * a (n - 2) + a (n - 3) := by
  sorry

end OMA.S_oeis_a253503

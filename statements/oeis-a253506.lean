import Mathlib

/-!
# OEIS A253506: Barker's generating function and recurrence, and Hardin's empirical polynomial

Source: https://oeis.org/A253506 (OEIS Foundation, CC BY-SA 4.0).

Entry (R. H. Hardin, Jan 02 2015), offset 1: Number of (n+2) X (4+2) 0..1 arrays with every 2 X 2
and 3 X 3 subblock diagonal maximum minus antidiagonal minimum nondecreasing horizontally and
vertically. Data: 636, 1196, 2088, 3400, 5136, 7396, ... The formula section states: Empirical: a(n) =
(1/3)*n^4 + 6*n^3 + (329/3)*n^2 + 288*n - 12 for n>6. Conjectures from _Colin Barker_, Dec 16 2018: (Start) G.f.:
4*x*(159 - 496*x + 617*x^2 - 360*x^3 + 59*x^4 + 45*x^5 - 35*x^6 + 20*x^7 - 9*x^8 + 3*x^9 - x^10) / (1 - x)^5. a(n) = 5*a(n-1) - ... for n>11. (End)

Formalization notes (the same conventions as the merged statement of the sibling A253503):
* An (n+2) X 6 array over 0..1 is a function `Fin (n + 2) → Fin 6 → Fin 2`, x i j being the element
  in row i and column j, both counted from 0; `get` reads it as an integer (0 outside, which no
  condition reaches).
* The diagonal of the s X s subblock with upper left element (i, j) is (i, j), (i+1, j+1), ..., and
  its antidiagonal is (i, j+s-1), (i+1, j+s-2), ..., (i+s-1, j); `f2` and `f3` give the diagonal
  maximum minus the antidiagonal minimum for s = 2 and s = 3.
* Nondecreasing horizontally and vertically: for each size, the value of a subblock is at most the
  value of the subblock of the same size one column to its right and of the one one row below,
  whenever that subblock lies inside the array (`good`).
* `a n` is `Set.ncard` of the set of these arrays, a set of functions between finite types.
* The g.f. is A(x) = Sum_{n >= 1} a(n) x^n (offset 1; the count for n = 0 is not a term of the
  sequence and is replaced by 0), stated as A(x) (1 - x)^5 = x P(x) in Z[[x]], which is equivalent
  because (1 - x)^5 has constant term 1. The recurrence is stated in the integers for n > 11, and the
  empirical polynomial in the rationals for n > 6, as in the entry.
* `main` is the conjunction of the three formulas.
-/

namespace OMA.S_oeis_a253506

open PowerSeries

/-- The element of the R X 6 array x in row r and column c, both counted from 0, as an integer, or 0
outside the array (the conditions below read only elements inside). -/
def get (R : ℕ) (x : Fin R → Fin 6 → Fin 2) (r c : ℕ) : ℤ :=
  if h : r < R ∧ c < 6 then ((x ⟨r, h.1⟩ ⟨c, h.2⟩).val : ℤ) else 0

/-- The diagonal maximum minus the antidiagonal minimum of the 2 X 2 subblock with upper left element
(i, j): the diagonal is (i, j), (i+1, j+1) and the antidiagonal (i, j+1), (i+1, j). -/
def f2 (R : ℕ) (x : Fin R → Fin 6 → Fin 2) (i j : ℕ) : ℤ :=
  max (get R x i j) (get R x (i + 1) (j + 1)) - min (get R x i (j + 1)) (get R x (i + 1) j)

/-- The diagonal maximum minus the antidiagonal minimum of the 3 X 3 subblock with upper left element
(i, j): the diagonal is (i, j), (i+1, j+1), (i+2, j+2) and the antidiagonal (i, j+2), (i+1, j+1),
(i+2, j). -/
def f3 (R : ℕ) (x : Fin R → Fin 6 → Fin 2) (i j : ℕ) : ℤ :=
  max (max (get R x i j) (get R x (i + 1) (j + 1))) (get R x (i + 2) (j + 2)) -
    min (min (get R x i (j + 2)) (get R x (i + 1) (j + 1))) (get R x (i + 2) j)

/-- The values of the 2 X 2 subblocks and those of the 3 X 3 subblocks are nondecreasing horizontally
and vertically: the value of each subblock is at most that of the subblock of the same size one
column to its right and that of the subblock one row below, when that subblock lies inside the
array. -/
def good (R : ℕ) (x : Fin R → Fin 6 → Fin 2) : Prop :=
  (∀ i j : ℕ, i + 2 ≤ R → j + 2 ≤ 6 →
      (j + 3 ≤ 6 → f2 R x i j ≤ f2 R x i (j + 1)) ∧ (i + 3 ≤ R → f2 R x i j ≤ f2 R x (i + 1) j)) ∧
    (∀ i j : ℕ, i + 3 ≤ R → j + 3 ≤ 6 →
      (j + 4 ≤ 6 → f3 R x i j ≤ f3 R x i (j + 1)) ∧ (i + 4 ≤ R → f3 R x i j ≤ f3 R x (i + 1) j))

/-- A253506(n): the number of (n+2) X 6 arrays over 0..1 with every 2 X 2 and 3 X 3 subblock diagonal
maximum minus antidiagonal minimum nondecreasing horizontally and vertically. -/
noncomputable def a (n : ℕ) : ℕ := Set.ncard {x : Fin (n + 2) → Fin 6 → Fin 2 | good (n + 2) x}

/-- Barker's conjectures (the g.f. and the recurrence) and the empirical polynomial of the entry. -/
theorem main :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℤ) else a n) * (1 - X) ^ 5 =
      4 * X * (159 - 496 * X + 617 * X ^ 2 - 360 * X ^ 3 + 59 * X ^ 4 + 45 * X ^ 5 - 35 * X ^ 6 + 20 * X ^ 7 - 9 * X ^ 8 + 3 * X ^ 9 - X ^ 10) ∧
    (∀ n : ℕ, 11 < n → (a n : ℤ) = 5 * a (n - 1) - 10 * a (n - 2) + 10 * a (n - 3) - 5 * a (n - 4) + a (n - 5)) ∧
    (∀ n : ℕ, 6 < n → (a n : ℚ) = (1 / 3 : ℚ) * (n : ℚ) ^ 4 + (6 : ℚ) * (n : ℚ) ^ 3 + (329 / 3 : ℚ) * (n : ℚ) ^ 2 + (288 : ℚ) * (n : ℚ) + (-12 : ℚ)) := by
  sorry

end OMA.S_oeis_a253506

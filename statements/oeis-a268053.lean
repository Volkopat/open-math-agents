import Mathlib

/-!
# OEIS A268053: Barker's generating function and closed form

Source: https://oeis.org/A268053 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry (R. H. Hardin, Jan 25 2016), offset 1: Number of n X 5 0..2 arrays with new values introduced
in each row and column in sequential order starting with zero. Data: 1, 16, 422, 14554, 560778, ...
The formula section states: Empirical: a(n) = 62*a(n-1) - 969*a(n-2) + 4568*a(n-3) - 5740*a(n-4).
Conjectures from _Colin Barker_, Jan 11 2019: (Start) G.f.: x*(1 - 46*x + 399*x^2 - 674*x^3) / ((1 -
2*x)*(1 - 5*x)*(1 - 14*x)*(1 - 41*x)). a(n) = (38745*2^n + 127428*5^n + 17425*2^(2+n)*7^n +
9800*41^n) / 2092230. (End)

Formalization notes:
* An n X 5 array over 0..2 is a function `Fin n → Fin 5 → Fin 3`, x i j being the element in row i
  and column j, both counted from 0.
* New values introduced in a row (or column) in sequential order starting with zero: reading the row
  from left to right (the column from top to bottom), every element other than 0 comes after an
  element of the same row (column) one less; `rowsNew` and `colsNew` say this for every row and
  every column. In particular the first row and the first column are 0.
* `a n` is `Set.ncard` of the set of these arrays, a set of functions between finite types.
* The g.f. is A(x) = Sum_{n >= 1} a(n) x^n (offset 1; the count for n = 0 is not a term of the
  sequence and is replaced by 0), stated as A(x) times the denominator = the numerator in Z[[x]],
  which is equivalent because the denominator has constant term 1. The closed form is stated in the
  rationals for n >= 1, where the division is exact.
* `main` is the conjunction of Barker's conjectures.
* Controls proved in the proof file: a(1..9), all the entry's listed terms.
-/

namespace OMA.S_oeis_a268053

open PowerSeries

/-- New values are introduced in each row in sequential order starting with zero: reading each row
from left to right, every element other than 0 comes after an element of its row one less. -/
def rowsNew (n : ℕ) (x : Fin n → Fin 5 → Fin 3) : Prop :=
  ∀ i j, x i j ≠ 0 → ∃ j', j' < j ∧ (x i j').val + 1 = (x i j).val

/-- New values are introduced in each column in sequential order starting with zero: reading each
column from top to bottom, every element other than 0 comes after an element of its column one
less. -/
def colsNew (n : ℕ) (x : Fin n → Fin 5 → Fin 3) : Prop :=
  ∀ i j, x i j ≠ 0 → ∃ i', i' < i ∧ (x i' j).val + 1 = (x i j).val

/-- A268053(n): the number of n X 5 arrays over 0..2 with new values introduced in each row and
column in sequential order starting with zero. -/
noncomputable def a (n : ℕ) : ℕ := Set.ncard {x : Fin n → Fin 5 → Fin 3 | rowsNew n x ∧ colsNew n x}

/-- Barker's conjectures: the g.f. and the closed form. -/
theorem main :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℤ) else a n) * ((1 - 2 * X) * (1 - 5 * X) * (1 - 14 * X) * (1 - 41 * X)) = X * (1 - 46 * X + 399 * X ^ 2 - 674 * X ^ 3) ∧
    ∀ n : ℕ, 1 ≤ n → (a n : ℚ) = (38745 * 2 ^ n + 127428 * 5 ^ n + 17425 * 2 ^ (2 + n) * 7 ^ n + 9800 * 41 ^ n) /
      2092230 := by
  sorry

end OMA.S_oeis_a268053

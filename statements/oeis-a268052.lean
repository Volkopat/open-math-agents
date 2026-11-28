import Mathlib

/-!
# OEIS A268052: Barker's generating function and closed form

Source: https://oeis.org/A268052 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry (R. H. Hardin, Jan 25 2016), offset 1: Number of n X 4 0..2 arrays with new values introduced
in each row and column in sequential order starting with zero. Data: 1, 8, 86, 1082, 14554, ... The
formula section states: Empirical: a(n) = 21*a(n-1) - 108*a(n-2) + 140*a(n-3). Conjectures from
_Colin Barker_, Jan 11 2019: (Start) G.f.: x*(1 - 13*x + 26*x^2) / ((1 - 2*x)*(1 - 5*x)*(1 - 14*x)).
a(n) = (105*2^n + 196*5^n + 25*2^(1+n)*7^n) / 1890. (End)

Formalization notes:
* An n X 4 array over 0..2 is a function `Fin n → Fin 4 → Fin 3`, x i j being the element in row i
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
* Controls proved in the proof file: a(1..10), all the entry's listed terms.
-/

namespace OMA.S_oeis_a268052

open PowerSeries

/-- New values are introduced in each row in sequential order starting with zero: reading each row
from left to right, every element other than 0 comes after an element of its row one less. -/
def rowsNew (n : ℕ) (x : Fin n → Fin 4 → Fin 3) : Prop :=
  ∀ i j, x i j ≠ 0 → ∃ j', j' < j ∧ (x i j').val + 1 = (x i j).val

/-- New values are introduced in each column in sequential order starting with zero: reading each
column from top to bottom, every element other than 0 comes after an element of its column one
less. -/
def colsNew (n : ℕ) (x : Fin n → Fin 4 → Fin 3) : Prop :=
  ∀ i j, x i j ≠ 0 → ∃ i', i' < i ∧ (x i' j).val + 1 = (x i j).val

/-- A268052(n): the number of n X 4 arrays over 0..2 with new values introduced in each row and
column in sequential order starting with zero. -/
noncomputable def a (n : ℕ) : ℕ := Set.ncard {x : Fin n → Fin 4 → Fin 3 | rowsNew n x ∧ colsNew n x}

/-- Barker's conjectures: the g.f. and the closed form. -/
theorem main :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℤ) else a n) * ((1 - 2 * X) * (1 - 5 * X) * (1 - 14 * X)) = X * (1 - 13 * X + 26 * X ^ 2) ∧
    ∀ n : ℕ, 1 ≤ n → (a n : ℚ) = (105 * 2 ^ n + 196 * 5 ^ n + 25 * 2 ^ (1 + n) * 7 ^ n) / 1890 := by
  sorry

end OMA.S_oeis_a268052

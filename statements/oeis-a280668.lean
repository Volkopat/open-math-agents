import Mathlib

/-!
# OEIS A280668: Barker's generating function and closed form

Source: https://oeis.org/A280668 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry (R. H. Hardin, Jan 07 2017), offset 1: Number of n X 3 0..2 arrays with no element equal to
more than one of its horizontal and antidiagonal neighbors and with new values introduced in order 0
sequentially upwards. Data: 4, 59, 858, 12484, 181640, ... The formula section states: Empirical:
a(n) = 14*a(n-1) + 8*a(n-2). Conjectures from _Colin Barker_, Feb 14 2019: (Start) G.f.: x*(4 + 3*x)
/ (1 - 14*x - 8*x^2). a(n) = ((7-sqrt(57))^n*(-11+3*sqrt(57)) + (7+sqrt(57))^n*(11+3*sqrt(57))) /
(16*sqrt(57)). (End)

Formalization notes:
* An n X 3 array over 0..2 is a function `Fin n → Fin 3 → Fin 3`, x i j being the element in row i
  and column j, both counted from 0. `cell n x r c` is the element at the integer coordinates (r,
  c), or none outside the array. The horizontal neighbors of the element at (i, j) are the elements
  at the offsets (0,-1) and (0,1), and its antidiagonal neighbors those at (-1,1) and (1,-1). `nbrs`
  lists the values of those that lie inside the array.
* An element is equal to more than one of its neighbors when at least two of them are equal to it
  (`eqmore`); the entry counts the arrays in which no element is.
* New values introduced in order: reading the array row by row from the top, each row from left to
  right, every element other than 0 comes after an element one less (`ordered`).
* `a n` is `Set.ncard` of the set of these arrays, a set of functions between finite types.
* The g.f. is A(x) = Sum_{n >= 1} a(n) x^n (offset 1; the count for n = 0 is not a term of the
  sequence and is replaced by 0), stated as A(x) (1 - 14x - 8x^2) = x (4 + 3x) in Z[[x]], which is
  equivalent because 1 - 14x - 8x^2 has constant term 1. The closed form is stated in the reals for
  n >= 1.
* `main` is the conjunction of Barker's conjectures.
* Controls proved in the proof file: a(1..16), all the entry's listed terms.
-/

namespace OMA.S_oeis_a280668

open PowerSeries

/-- The element of the n X 3 array x in row r and column c, both counted from 0, or none when
(r, c) lies outside the array. -/
def cell (n : ℕ) (x : Fin n → Fin 3 → Fin 3) (r c : ℤ) : Option (Fin 3) :=
  if h : 0 ≤ r ∧ r < n ∧ 0 ≤ c ∧ c < 3 then
    some (x ⟨r.toNat, by omega⟩ ⟨c.toNat, by omega⟩)
  else none

/-- The values of the horizontal and antidiagonal neighbors of the element in row i and
column j: the elements at the offsets (row, column) (0,-1), (0,1), (-1,1), (1,-1) that lie inside
the array. -/
def nbrs (n : ℕ) (x : Fin n → Fin 3 → Fin 3) (i : Fin n) (j : Fin 3) : List (Fin 3) :=
  [((0 : ℤ), (-1 : ℤ)), (0, 1), (-1, 1), (1, -1)].filterMap fun d => cell n x (i + d.1) (j + d.2)

/-- The element in row i and column j is equal to more than one of its horizontal and antidiagonal
neighbors. -/
def eqmore (n : ℕ) (x : Fin n → Fin 3 → Fin 3) (i : Fin n) (j : Fin 3) : Prop :=
  1 < (nbrs n x i j).count (x i j)

/-- New values are introduced in order 0 sequentially upwards: reading the array row by row from
the top, each row from left to right, every element other than 0 comes after an element one less. -/
def ordered (n : ℕ) (x : Fin n → Fin 3 → Fin 3) : Prop :=
  ∀ i j, x i j ≠ 0 → ∃ i' j', (i' < i ∨ (i' = i ∧ j' < j)) ∧ (x i' j').val + 1 = (x i j).val

/-- A280668(n): the number of n X 3 arrays over 0..2 in which no element is equal to more than
one of its horizontal and antidiagonal neighbors, with new values introduced in order. -/
noncomputable def a (n : ℕ) : ℕ :=
  Set.ncard {x : Fin n → Fin 3 → Fin 3 | (∀ i j, ¬ eqmore n x i j) ∧ ordered n x}

/-- Barker's conjectures: the g.f. and the closed form. -/
theorem main :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℤ) else a n) * (1 - 14 * X - 8 * X ^ 2) = X * (4 + 3 * X) ∧
    ∀ n : ℕ, 1 ≤ n → (a n : ℝ) = ((7 - Real.sqrt 57) ^ n * (-11 + 3 * Real.sqrt 57) +
      (7 + Real.sqrt 57) ^ n * (11 + 3 * Real.sqrt 57)) / (16 * Real.sqrt 57) := by
  sorry

end OMA.S_oeis_a280668

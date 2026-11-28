import Mathlib

/-!
# OEIS A279735: Barker's generating function and closed form

Source: https://oeis.org/A279735 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry (R. H. Hardin, Dec 18 2016), offset 1: Number of n X 2 0..1 arrays with no element equal to a
strict majority of its horizontal and antidiagonal neighbors, with the exception of exactly one
element, and with new values introduced in order 0 sequentially upwards. Data: 0, 2, 8, 26, 80, ...
The formula section states: Empirical: a(n) = 6*a(n-1) - 11*a(n-2) + 6*a(n-3) - a(n-4). Conjectures
from _Colin Barker_, Feb 11 2019: (Start) G.f.: 2*x^2*(1 - 2*x) / (1 - 3*x + x^2)^2. a(n) =
(-1)*(2^(1-n)*(sqrt(5)*((3-sqrt(5))^n-(3+sqrt(5))^n) + 5*(3-sqrt(5))^n*(2+sqrt(5))*n -
5*(-2+sqrt(5))*(3+sqrt(5))^n*n)) / 25. (End)

Formalization notes:
* An n X 2 array over 0..1 is a function `Fin n → Fin 2 → Fin 2`, x i j being the element in row i
  and column j, both counted from 0. `cell n x r c` is the element at the integer coordinates (r,
  c), or none outside the array. The horizontal neighbors of the element at (i, j) are the elements
  at the offsets (0,-1) and (0,1), and its antidiagonal neighbors those at (-1,1) and (1,-1). `nbrs`
  lists the values of those that lie inside the array.
* An element is equal to a strict majority of its neighbors when more than half of them are equal to
  it (`maj`). The entry counts the arrays in which no element has this property with the exception
  of exactly one element, so the set of elements with it has exactly one member.
* New values introduced in order: reading the array row by row from the top, each row from left to
  right, every element other than 0 comes after an element one less (`ordered`), which for 0..1
  arrays says that the first element is 0.
* `a n` is `Set.ncard` of the set of these arrays, a set of functions between finite types.
* The g.f. is A(x) = Sum_{n >= 1} a(n) x^n (offset 1; the count for n = 0 is not a term of the
  sequence and is replaced by 0), stated as A(x) (1 - 3x + x^2)^2 = 2x^2 (1 - 2x) in Z[[x]], which
  is equivalent because (1 - 3x + x^2)^2 has constant term 1. The closed form is stated in the reals
  for n >= 1, with 2^(1-n) as an integer power.
* `main` is the conjunction of Barker's conjectures.
* Controls proved in the proof file: a(1..14), all the entry's listed terms.
-/

namespace OMA.S_oeis_a279735

open PowerSeries

/-- The element of the n X 2 array x in row r and column c, both counted from 0, or none when
(r, c) lies outside the array. -/
def cell (n : ℕ) (x : Fin n → Fin 2 → Fin 2) (r c : ℤ) : Option (Fin 2) :=
  if h : 0 ≤ r ∧ r < n ∧ 0 ≤ c ∧ c < 2 then
    some (x ⟨r.toNat, by omega⟩ ⟨c.toNat, by omega⟩)
  else none

/-- The values of the horizontal and antidiagonal neighbors of the element in row i and column j: the elements at
the offsets (row, column) (0,-1), (0,1), (-1,1), (1,-1) that lie inside the array. -/
def nbrs (n : ℕ) (x : Fin n → Fin 2 → Fin 2) (i : Fin n) (j : Fin 2) : List (Fin 2) :=
  [((0 : ℤ), (-1 : ℤ)), (0, 1), (-1, 1), (1, -1)].filterMap fun d => cell n x (i + d.1) (j + d.2)

/-- The element in row i and column j is equal to a strict majority of its horizontal and antidiagonal
neighbors: more than half of them are equal to it. -/
def maj (n : ℕ) (x : Fin n → Fin 2 → Fin 2) (i : Fin n) (j : Fin 2) : Prop :=
  (nbrs n x i j).length < 2 * (nbrs n x i j).count (x i j)

/-- New values are introduced in order 0 sequentially upwards: reading the array row by row from
the top, each row from left to right, every element other than 0 comes after an element one less. -/
def ordered (n : ℕ) (x : Fin n → Fin 2 → Fin 2) : Prop :=
  ∀ i j, x i j ≠ 0 → ∃ i' j', (i' < i ∨ (i' = i ∧ j' < j)) ∧ (x i' j').val + 1 = (x i j).val

/-- A279735(n): the number of n X 2 arrays over 0..1 in which exactly one element is
equal to a strict majority of its horizontal and antidiagonal neighbors, with new values
introduced in order. -/
noncomputable def a (n : ℕ) : ℕ :=
  Set.ncard {x : Fin n → Fin 2 → Fin 2 |
    {p : Fin n × Fin 2 | maj n x p.1 p.2}.ncard = 1 ∧ ordered n x}

/-- Barker's conjectures: the g.f. and the closed form. -/
theorem main :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℤ) else a n) * ((1 - 3 * X + X ^ 2) ^ 2) = 2 * X ^ 2 * (1 - 2 * X) ∧
    ∀ n : ℕ, 1 ≤ n → (a n : ℝ) = -1 * (2 ^ ((1 : ℤ) - n) * (Real.sqrt 5 * ((3 - Real.sqrt 5) ^ n - (3 + Real.sqrt 5) ^ n) +
      5 * (3 - Real.sqrt 5) ^ n * (2 + Real.sqrt 5) * n -
      5 * (-2 + Real.sqrt 5) * (3 + Real.sqrt 5) ^ n * n)) / 25 := by
  sorry

end OMA.S_oeis_a279735

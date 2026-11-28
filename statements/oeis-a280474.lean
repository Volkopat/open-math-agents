import Mathlib

/-!
# OEIS A280474: Barker's generating function and closed form

Source: https://oeis.org/A280474 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry (R. H. Hardin, Jan 04 2017), offset 1: Number of n X 2 0..2 arrays with no element unequal to
a strict majority of its horizontal and antidiagonal neighbors, with the exception of exactly two
elements, and with new values introduced in order 0 sequentially upwards. Data: 1, 6, 30, 158, 846,
... The formula section states: Empirical: a(n) = 15*a(n-1) - 87*a(n-2) + 245*a(n-3) - 348*a(n-4) +
240*a(n-5) - 64*a(n-6). Conjectures from _Colin Barker_, Feb 13 2019: (Start) G.f.: x*(1 - 3*x)*(1 -
6*x + 9*x^2 + 12*x^3) / ((1 - x)^3*(1 - 4*x)^3). a(n) = (8*(4^n-1) + 21*4^n*n + 6*(32+4^n)*n^2) /
324. (End)

Formalization notes:
* An n X 2 array over 0..2 is a function `Fin n → Fin 2 → Fin 3`, x i j being the element in row i
  and column j, both counted from 0. `cell n x r c` is the element at the integer coordinates (r,
  c), or none outside the array. The horizontal neighbors of the element at (i, j) are the elements
  at the offsets (0,-1) and (0,1), and its antidiagonal neighbors those at (-1,1) and (1,-1). `nbrs`
  lists the values of those that lie inside the array.
* An element is unequal to a strict majority of its neighbors when more than half of them are
  unequal to it (`unmaj`). The entry counts the arrays in which no element has this property with
  the exception of exactly two elements, so the set of elements with it has exactly two members.
* New values introduced in order: reading the array row by row from the top, each row from left to
  right, every element other than 0 comes after an element one less (`ordered`).
* `a n` is `Set.ncard` of the set of these arrays, a set of functions between finite types.
* The g.f. is A(x) = Sum_{n >= 1} a(n) x^n (offset 1; the count for n = 0 is not a term of the
  sequence and is replaced by 0), stated as A(x) (1 - x)^3 (1 - 4x)^3 = x (1 - 3x)(1 - 6x + 9x^2 +
  12x^3) in Z[[x]], which is equivalent because (1 - x)^3 (1 - 4x)^3 has constant term 1. The closed
  form is stated in the rationals for n >= 1, where the division by 324 is exact.
* `main` is the conjunction of Barker's conjectures.
* Controls proved in the proof file: a(1..12), all the entry's listed terms.
-/

namespace OMA.S_oeis_a280474

open PowerSeries

/-- The element of the n X 2 array x in row r and column c, both counted from 0, or none when
(r, c) lies outside the array. -/
def cell (n : ℕ) (x : Fin n → Fin 2 → Fin 3) (r c : ℤ) : Option (Fin 3) :=
  if h : 0 ≤ r ∧ r < n ∧ 0 ≤ c ∧ c < 2 then
    some (x ⟨r.toNat, by omega⟩ ⟨c.toNat, by omega⟩)
  else none

/-- The values of the horizontal and antidiagonal neighbors of the element in row i and
column j: the elements at the offsets (row, column) (0,-1), (0,1), (-1,1), (1,-1) that lie inside
the array. -/
def nbrs (n : ℕ) (x : Fin n → Fin 2 → Fin 3) (i : Fin n) (j : Fin 2) : List (Fin 3) :=
  [((0 : ℤ), (-1 : ℤ)), (0, 1), (-1, 1), (1, -1)].filterMap fun d => cell n x (i + d.1) (j + d.2)

/-- The element in row i and column j is unequal to a strict majority of its horizontal and antidiagonal
neighbors: more than half of them are unequal to it. -/
def unmaj (n : ℕ) (x : Fin n → Fin 2 → Fin 3) (i : Fin n) (j : Fin 2) : Prop :=
  (nbrs n x i j).length < 2 * (nbrs n x i j).countP (· ≠ x i j)

/-- New values are introduced in order 0 sequentially upwards: reading the array row by row from
the top, each row from left to right, every element other than 0 comes after an element one less. -/
def ordered (n : ℕ) (x : Fin n → Fin 2 → Fin 3) : Prop :=
  ∀ i j, x i j ≠ 0 → ∃ i' j', (i' < i ∨ (i' = i ∧ j' < j)) ∧ (x i' j').val + 1 = (x i j).val

/-- A280474(n): the number of n X 2 arrays over 0..2 in which exactly two elements are
unequal to a strict majority of their horizontal and antidiagonal neighbors, with new values
introduced in order. -/
noncomputable def a (n : ℕ) : ℕ :=
  Set.ncard {x : Fin n → Fin 2 → Fin 3 |
    {p : Fin n × Fin 2 | unmaj n x p.1 p.2}.ncard = 2 ∧ ordered n x}

/-- Barker's conjectures: the g.f. and the closed form. -/
theorem main :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℤ) else a n) * ((1 - X) ^ 3 * (1 - 4 * X) ^ 3) = X * (1 - 3 * X) * (1 - 6 * X + 9 * X ^ 2 + 12 * X ^ 3) ∧
    ∀ n : ℕ, 1 ≤ n → (a n : ℚ) = (8 * (4 ^ n - 1) + 21 * 4 ^ n * n + 6 * (32 + 4 ^ n) * n ^ 2) / 324 := by
  sorry

end OMA.S_oeis_a280474

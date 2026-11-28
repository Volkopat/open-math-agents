import Mathlib

/-!
# OEIS A279262: Barker's generating function and closed form

Source: https://oeis.org/A279262 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry (R. H. Hardin, Dec 08 2016), offset 1: Number of n X 2 0..1 arrays with no element equal to a
strict majority of its horizontal and vertical neighbors, with the exception of exactly one element,
and with new values introduced in order 0 sequentially upwards. Data: 0, 4, 10, 20, 38, ... The
formula section states: Empirical: a(n) = 3*a(n-1) - a(n-2) - 3*a(n-3) + a(n-4) + a(n-5).
Conjectures from _Colin Barker_, Feb 26 2018: (Start) G.f.: 2*x^2*(1 + x)*(2 - 3*x) / ((1 - x)*(1 -
x - x^2)^2). a(n) = (1/25)*(2^(-n)*(-25*2^(2+n)+(50-6*sqrt(5))*(1-sqrt(5))^n + 50*(1+sqrt(5))^n +
6*sqrt(5)*(1+sqrt(5))^n - 5*(1-sqrt(5))^n*(1+sqrt(5))*n + 5*(-1+sqrt(5))*(1+sqrt(5))^n*n)). (End)

Formalization notes:
* An n X 2 array over 0..1 is a function `Fin n → Fin 2 → Fin 2`, x i j being the element in row i
  and column j, both counted from 0. `cell n x r c` is the element at the integer coordinates (r,
  c), or none outside the array. The horizontal neighbors of the element at (i, j) are the elements
  at the offsets (0,-1) and (0,1), and its vertical neighbors those at (-1,0) and (1,0). `nbrs`
  lists the values of those that lie inside the array.
* An element is equal to a strict majority of its neighbors when more than half of them are equal to
  it (`maj`). The entry counts the arrays in which no element has this property with the exception
  of exactly one element, so the set of elements with it has exactly one member.
* New values introduced in order: reading the array row by row from the top, each row from left to
  right, every element other than 0 comes after an element one less (`ordered`), which for 0..1
  arrays says that the first element is 0.
* `a n` is `Set.ncard` of the set of these arrays, a set of functions between finite types.
* The g.f. is A(x) = Sum_{n >= 1} a(n) x^n (offset 1; the count for n = 0 is not a term of the
  sequence and is replaced by 0), stated as A(x) (1 - x)(1 - x - x^2)^2 = 2x^2 (1 + x)(2 - 3x) in
  Z[[x]], which is equivalent because (1 - x)(1 - x - x^2)^2 has constant term 1. The closed form is
  stated in the reals for n >= 1, with 2^(-n) as an integer power.
* `main` is the conjunction of Barker's conjectures.
* Controls proved in the proof file: a(1..17), all the entry's listed terms.
-/

namespace OMA.S_oeis_a279262

open PowerSeries

/-- The element of the n X 2 array x in row r and column c, both counted from 0, or none when
(r, c) lies outside the array. -/
def cell (n : ℕ) (x : Fin n → Fin 2 → Fin 2) (r c : ℤ) : Option (Fin 2) :=
  if h : 0 ≤ r ∧ r < n ∧ 0 ≤ c ∧ c < 2 then
    some (x ⟨r.toNat, by omega⟩ ⟨c.toNat, by omega⟩)
  else none

/-- The values of the horizontal and vertical neighbors of the element in row i and column j:
the elements at the offsets (row, column) (0,-1), (0,1), (-1,0), (1,0) that lie inside the
array. -/
def nbrs (n : ℕ) (x : Fin n → Fin 2 → Fin 2) (i : Fin n) (j : Fin 2) : List (Fin 2) :=
  [((0 : ℤ), (-1 : ℤ)), (0, 1), (-1, 0), (1, 0)].filterMap fun d => cell n x (i + d.1) (j + d.2)

/-- The element in row i and column j is equal to a strict majority of its horizontal and vertical
neighbors: more than half of them are equal to it. -/
def maj (n : ℕ) (x : Fin n → Fin 2 → Fin 2) (i : Fin n) (j : Fin 2) : Prop :=
  (nbrs n x i j).length < 2 * (nbrs n x i j).count (x i j)

/-- New values are introduced in order 0 sequentially upwards: reading the array row by row from
the top, each row from left to right, every element other than 0 comes after an element one less. -/
def ordered (n : ℕ) (x : Fin n → Fin 2 → Fin 2) : Prop :=
  ∀ i j, x i j ≠ 0 → ∃ i' j', (i' < i ∨ (i' = i ∧ j' < j)) ∧ (x i' j').val + 1 = (x i j).val

/-- A279262(n): the number of n X 2 arrays over 0..1 in which exactly one element is
equal to a strict majority of its horizontal and vertical neighbors, with new values
introduced in order. -/
noncomputable def a (n : ℕ) : ℕ :=
  Set.ncard {x : Fin n → Fin 2 → Fin 2 |
    {p : Fin n × Fin 2 | maj n x p.1 p.2}.ncard = 1 ∧ ordered n x}

/-- Barker's conjectures: the g.f. and the closed form. -/
theorem main :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℤ) else a n) * ((1 - X) * (1 - X - X ^ 2) ^ 2) = 2 * X ^ 2 * (1 + X) * (2 - 3 * X) ∧
    ∀ n : ℕ, 1 ≤ n → (a n : ℝ) = 1 / 25 * (2 ^ (-(n : ℤ)) * (-25 * 2 ^ (2 + n) + (50 - 6 * Real.sqrt 5) * (1 - Real.sqrt 5) ^ n +
      50 * (1 + Real.sqrt 5) ^ n + 6 * Real.sqrt 5 * (1 + Real.sqrt 5) ^ n -
      5 * (1 - Real.sqrt 5) ^ n * (1 + Real.sqrt 5) * n +
      5 * (-1 + Real.sqrt 5) * (1 + Real.sqrt 5) ^ n * n)) := by
  sorry

end OMA.S_oeis_a279262

import Mathlib

/-!
# OEIS A277761: Barker's generating function and closed form

Source: https://oeis.org/A277761 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry (R. H. Hardin, Oct 29 2016), offset 1: Number of n X 2 0..2 arrays with every element equal to
some element at offset (-1,-1) (-1,0) (-1,1) (0,-1) (0,1) or (1,0) both plus 1 mod 3 and minus 1 mod
3, with new values introduced in order 0..2. Data: 0, 1, 2, 14, 56, ... The formula section states:
Empirical: a(n) = 4*a(n-1) + 6*a(n-2) - 12*a(n-3). Conjectures from _Colin Barker_, Feb 05 2019:
(Start) G.f.: x^2*(1 - 2*x) / ((1 + 2*x)*(1 - 6*x + 6*x^2)). a(n) = (3*(-1)^n*2^(2+n) -
(-5+sqrt(3))*(3+sqrt(3))^n + (3-sqrt(3))^n*(5+sqrt(3))) / 132. (End)

Formalization notes:
* An n X 2 array over 0..2 is a function `Fin n → Fin 2 → Fin 3`, x i j being the element in row i
  and column j, both counted from 0. `cell n x r c` is the element at the integer coordinates (r,
  c), or none outside the array. The elements considered for the element at (i, j) are those at the
  offsets (-1,-1), (-1,0), (-1,1), (0,-1), (0,1) and (1,0). `nbrs` lists the values of those that
  lie inside the array.
* The condition of the entry for an element x is that it is equal to some of these elements plus 1
  mod 3 and to some of them minus 1 mod 3 (`both`, with the arithmetic of Fin 3, which is mod 3);
  every element must satisfy it.
* New values introduced in order: reading the array row by row from the top, each row from left to
  right, every element other than 0 comes after an element one less (`ordered`).
* `a n` is `Set.ncard` of the set of these arrays, a set of functions between finite types.
* The g.f. is A(x) = Sum_{n >= 1} a(n) x^n (offset 1; the count for n = 0 is not a term of the
  sequence and is replaced by 0), stated as A(x) (1 + 2x)(1 - 6x + 6x^2) = x^2 (1 - 2x) in Z[[x]],
  which is equivalent because (1 + 2x)(1 - 6x + 6x^2) has constant term 1. The closed form is stated
  in the reals for n >= 1.
* `main` is the conjunction of Barker's conjectures.
* Controls proved in the proof file: a(1..13), all the entry's listed terms.
-/

namespace OMA.S_oeis_a277761

open PowerSeries

/-- The element of the n X 2 array x in row r and column c, both counted from 0, or none when
(r, c) lies outside the array. -/
def cell (n : ℕ) (x : Fin n → Fin 2 → Fin 3) (r c : ℤ) : Option (Fin 3) :=
  if h : 0 ≤ r ∧ r < n ∧ 0 ≤ c ∧ c < 2 then
    some (x ⟨r.toNat, by omega⟩ ⟨c.toNat, by omega⟩)
  else none

/-- The values of the elements at the offsets (row, column) (-1,-1), (-1,0), (-1,1), (0,-1),
(0,1), (1,0) from the element in row i and column j that lie inside the array. -/
def nbrs (n : ℕ) (x : Fin n → Fin 2 → Fin 3) (i : Fin n) (j : Fin 2) : List (Fin 3) :=
  [((-1 : ℤ), (-1 : ℤ)), (-1, 0), (-1, 1), (0, -1), (0, 1), (1, 0)].filterMap fun d => cell n x (i + d.1) (j + d.2)

/-- The element in row i and column j is equal to some element at these offsets plus 1 mod 3 and
to some element at these offsets minus 1 mod 3 (the arithmetic of Fin 3 is mod 3). -/
def both (n : ℕ) (x : Fin n → Fin 2 → Fin 3) (i : Fin n) (j : Fin 2) : Prop :=
  (∃ y ∈ nbrs n x i j, x i j = y + 1) ∧ (∃ z ∈ nbrs n x i j, x i j = z - 1)

/-- New values are introduced in order 0 sequentially upwards: reading the array row by row from
the top, each row from left to right, every element other than 0 comes after an element one less. -/
def ordered (n : ℕ) (x : Fin n → Fin 2 → Fin 3) : Prop :=
  ∀ i j, x i j ≠ 0 → ∃ i' j', (i' < i ∨ (i' = i ∧ j' < j)) ∧ (x i' j').val + 1 = (x i j).val

/-- A277761(n): the number of n X 2 arrays over 0..2 in which every element is equal to some
element at those offsets plus 1 mod 3 and to some minus 1 mod 3, with new values introduced in
order. -/
noncomputable def a (n : ℕ) : ℕ :=
  Set.ncard {x : Fin n → Fin 2 → Fin 3 | (∀ i j, both n x i j) ∧ ordered n x}

/-- Barker's conjectures: the g.f. and the closed form. -/
theorem main :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℤ) else a n) * ((1 + 2 * X) * (1 - 6 * X + 6 * X ^ 2)) = X ^ 2 * (1 - 2 * X) ∧
    ∀ n : ℕ, 1 ≤ n → (a n : ℝ) = (3 * (-1) ^ n * 2 ^ (2 + n) - (-5 + Real.sqrt 3) * (3 + Real.sqrt 3) ^ n +
      (3 - Real.sqrt 3) ^ n * (5 + Real.sqrt 3)) / 132 := by
  sorry

end OMA.S_oeis_a277761

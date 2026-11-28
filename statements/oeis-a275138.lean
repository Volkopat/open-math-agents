import Mathlib

/-!
# OEIS A275138: Barker's generating function and closed form

Source: https://oeis.org/A275138 (OEIS Foundation, CC BY-SA 4.0).
Credit: @ceejcake

Entry (R. H. Hardin), offset 1: Number of n X 4 0..2 arrays with no element equal to any value at
offset (-2,-2) (-1,-2) or (0,-1) and new values introduced in order 0..2.
Data: 4, 48, 224, 1088, 5248, 25344, 122368, 590848, ...
Formula section: Conjectures from Colin Barker, Jan 31 2019:
G.f.: 4*x*(1 + 8*x + 4*x^2) / (1 - 4*x - 4*x^2).
a(n) = 2*((2-2*sqrt(2))^n + (2*(1+sqrt(2)))^n) for n>1.

Formalization notes:
* An array is `A : Fin n → Fin 4 → Fin 3`; `A i j` is the element in row `i`, column `j`.
* `entry A r c` is the element at integer position `(r, c)`, or `none` outside the array.
* An offset `(dr, dc)` is a change of row by `dr` and of column by `dc`. No element may equal the
  element at offset `(-2, -2)`, `(-1, -2)` or `(0, -1)` from it, when that position lies inside
  the array.
* New values 0..2 are introduced in order (row-major order): every value smaller than an element
  occurs at an earlier position (row-major index `4 * i + j`).
* This reading reproduces all 21 data terms of the entry (brute force for n <= 3 and a transfer
  count for all terms).
* The g.f. is Sum_(n >= 1) a(n) x^n (offset 1, so the constant coefficient is 0), stated as
  denominator times series equals numerator in the formal power series ring over the integers.
  The closed form is stated in the reals for n > 1, with sqrt as `Real.sqrt`.
-/

namespace OMA.S_oeis_a275138

open PowerSeries

/-- The element of the array `A` at the integer position `(r, c)`, or `none` when the position
lies outside the array. -/
def entry {n : ℕ} (A : Fin n → Fin 4 → Fin 3) (r c : ℤ) : Option (Fin 3) :=
  if h : 0 ≤ r ∧ r < n ∧ 0 ≤ c ∧ c < 4 then
    some (A ⟨r.toNat, by omega⟩ ⟨c.toNat, by omega⟩)
  else none

/-- The forbidden offsets (row change, column change). -/
def offsets : List (ℤ × ℤ) := [(-2, -2), (-1, -2), (0, -1)]

/-- No element is equal to the value at offset (-2,-2), (-1,-2) or (0,-1) from it. -/
def NoEqualAtOffsets {n : ℕ} (A : Fin n → Fin 4 → Fin 3) : Prop :=
  ∀ (i : Fin n) (j : Fin 4), ∀ d ∈ offsets, entry A (i + d.1) (j + d.2) ≠ some (A i j)

/-- New values are introduced in order 0..2 (in row-major order): every value smaller than an
element of the array occurs at an earlier position. -/
def NewValuesInOrder {n : ℕ} (A : Fin n → Fin 4 → Fin 3) : Prop :=
  ∀ (i : Fin n) (j : Fin 4) (w : Fin 3), w < A i j →
    ∃ (i' : Fin n) (j' : Fin 4), 4 * (i' : ℕ) + j' < 4 * (i : ℕ) + j ∧ A i' j' = w

/-- `NoEqualAtOffsets` is decidable (all quantifiers range over finite types). -/
instance {n : ℕ} : DecidablePred (NoEqualAtOffsets (n := n)) := fun A => by
  unfold NoEqualAtOffsets; infer_instance

/-- `NewValuesInOrder` is decidable (all quantifiers range over finite types). -/
instance {n : ℕ} : DecidablePred (NewValuesInOrder (n := n)) := fun A => by
  unfold NewValuesInOrder; infer_instance

/-- A275138(n): the number of n X 4 arrays with entries 0..2 with no element equal to the value
at offset (-2,-2), (-1,-2) or (0,-1), and new values introduced in order. -/
def a (n : ℕ) : ℕ :=
  (Finset.univ.filter fun A : Fin n → Fin 4 → Fin 3 =>
    NoEqualAtOffsets A ∧ NewValuesInOrder A).card

/-- Barker's conjectures for A275138 (offset 1): the generating function
4x(1 + 8x + 4x^2) / (1 - 4x - 4x^2), and the closed form for n > 1. -/
theorem main :
    (1 - 4 * X - 4 * X ^ 2) * mk (fun n => if n = 0 then 0 else (a n : ℤ)) =
      (4 * X * (1 + 8 * X + 4 * X ^ 2) : PowerSeries ℤ) ∧
    ∀ n : ℕ, 1 < n → (a n : ℝ) =
      2 * ((2 - 2 * Real.sqrt 2) ^ n + (2 * (1 + Real.sqrt 2)) ^ n) := by
  sorry

end OMA.S_oeis_a275138

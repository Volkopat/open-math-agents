import Mathlib

/-!
# OEIS A281199: Barker's generating function and closed form

Source: https://oeis.org/A281199 (OEIS Foundation, CC BY-SA 4.0).
Credit: @ceejcake

Entry (R. H. Hardin), offset 1: Number of n X 2 0..1 arrays with no element equal to more than
one of its horizontal and antidiagonal neighbors, with the exception of exactly one element, and
with new values introduced in order 0 sequentially upwards.
Data: 0, 2, 10, 38, 130, 420, 1308, 3970, 11822, ...
Formula section: Conjectures from Colin Barker, Feb 16 2019:
G.f.: 2*x^2*(1 - x) / (1 - 3*x + x^2)^2.
a(n) = (2^(-n)*(2*sqrt(5)*((3-sqrt(5))^n - (3+sqrt(5))^n) - 5*(3-sqrt(5))^n*(1+sqrt(5))*n
  + 5*(-1+sqrt(5))*(3+sqrt(5))^n*n)) / 25.

Formalization notes:
* An array is `A : Fin n → Fin 2 → Fin 2`; `A i j` is the element in row `i`, column `j`.
* `entry A r c` is the element at integer position `(r, c)`, or `none` outside the array.
* The horizontal and antidiagonal neighbours of `(i, j)` are the positions at offsets
  `(0, -1)`, `(0, 1)`, `(-1, 1)` and `(1, -1)` that lie inside the array.
* An element is an exception when it equals more than one of its neighbours; the array must have
  exactly one exception.
* New values are introduced in order 0 sequentially upwards, in row-major order: every value
  smaller than an element occurs at an earlier position (row-major index `2 * i + j`).
* This reading reproduces all 26 data terms of the entry (brute force for n <= 5 and a transfer
  count for all terms).
* The g.f. is Sum_(n >= 1) a(n) x^n (offset 1, so the constant coefficient is 0), stated as
  denominator times series equals numerator in the formal power series ring over the integers.
  The closed form is stated in the reals for n >= 1, with sqrt as `Real.sqrt`.
-/

namespace OMA.S_oeis_a281199

open PowerSeries

/-- The element of the array `A` at the integer position `(r, c)`, or `none` when the position
lies outside the array. -/
def entry {n : ℕ} (A : Fin n → Fin 2 → Fin 2) (r c : ℤ) : Option (Fin 2) :=
  if h : 0 ≤ r ∧ r < n ∧ 0 ≤ c ∧ c < 2 then
    some (A ⟨r.toNat, by omega⟩ ⟨c.toNat, by omega⟩)
  else none

/-- The offsets (row, column) of the horizontal and antidiagonal neighbours: left, right,
up-right and down-left. -/
def offsets : List (ℤ × ℤ) := [(0, -1), (0, 1), (-1, 1), (1, -1)]

/-- The number of horizontal and antidiagonal neighbours of the element at `(i, j)` that are
equal to it. -/
def equalNeighbours {n : ℕ} (A : Fin n → Fin 2 → Fin 2) (i : Fin n) (j : Fin 2) : ℕ :=
  (offsets.filter fun d => entry A (i + d.1) (j + d.2) = some (A i j)).length

/-- The exceptions: the positions whose element equals more than one of its horizontal and
antidiagonal neighbours. -/
def exceptions {n : ℕ} (A : Fin n → Fin 2 → Fin 2) : Finset (Fin n × Fin 2) :=
  Finset.univ.filter fun p => 1 < equalNeighbours A p.1 p.2

/-- New values are introduced in order 0 sequentially upwards (in row-major order): every value
smaller than an element of the array occurs at an earlier position. -/
def NewValuesInOrder {n : ℕ} (A : Fin n → Fin 2 → Fin 2) : Prop :=
  ∀ (i : Fin n) (j : Fin 2) (w : Fin 2), w < A i j →
    ∃ (i' : Fin n) (j' : Fin 2), 2 * (i' : ℕ) + j' < 2 * (i : ℕ) + j ∧ A i' j' = w

/-- `NewValuesInOrder` is decidable (all quantifiers range over finite types). -/
instance {n : ℕ} : DecidablePred (NewValuesInOrder (n := n)) := fun A => by
  unfold NewValuesInOrder; infer_instance

/-- A281199(n): the number of n X 2 binary arrays with new values introduced in order and with
exactly one element equal to more than one of its horizontal and antidiagonal neighbours. -/
def a (n : ℕ) : ℕ :=
  (Finset.univ.filter fun A : Fin n → Fin 2 → Fin 2 =>
    NewValuesInOrder A ∧ (exceptions A).card = 1).card

/-- Barker's conjectures for A281199 (offset 1): the generating function
2x^2(1 - x) / (1 - 3x + x^2)^2, and the closed form for n >= 1. -/
theorem main :
    (1 - 3 * X + X ^ 2) ^ 2 * mk (fun n => if n = 0 then 0 else (a n : ℤ)) =
      (2 * X ^ 2 * (1 - X) : PowerSeries ℤ) ∧
    ∀ n : ℕ, 1 ≤ n → (a n : ℝ) =
      (2 ^ (-(n : ℤ)) * (2 * Real.sqrt 5 * ((3 - Real.sqrt 5) ^ n - (3 + Real.sqrt 5) ^ n) -
        5 * (3 - Real.sqrt 5) ^ n * (1 + Real.sqrt 5) * n +
        5 * (-1 + Real.sqrt 5) * (3 + Real.sqrt 5) ^ n * n)) / 25 := by
  sorry

end OMA.S_oeis_a281199

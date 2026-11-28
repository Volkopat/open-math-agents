import Mathlib

/-!
# OEIS A208253: Barker's generating function and closed form

Source: https://oeis.org/A208253 (OEIS Foundation, CC BY-SA 4.0).
Credit: @ceejcake

Entry (R. H. Hardin), offset 1: Number of n X 3 0..2 arrays with new values 0..2 introduced in
row major order and no element equal to more than one of its immediate leftward or upward
neighbors. Data: 5, 96, 2040, 43344, 920928, 19566912, ...
Formula section: Conjectures from Colin Barker, Jun 29 2018:
G.f.: x*(1 - 2*x)*(5 - 4*x) / (1 - 22*x + 16*x^2).
a(n) = (1/32)*sqrt(3/35)*((11-sqrt(105))^n*(-13+sqrt(105)) + (11+sqrt(105))^n*(13+sqrt(105)))
for n>1.

Formalization notes:
* An n X 3 array over 0..2 is `A : Fin n → Fin 3 → Fin 3`, with `A i j` the entry in row `i`,
  column `j`. Row major order puts cell `(i', j')` before `(i, j)` when `i' < i`, or `i' = i`
  and `j' < j`.
* New values 0..2 are introduced in row major order when every value smaller than an entry
  already occurs at an earlier cell in row major order.
* The immediate leftward neighbor of `(i, j)` is `(i, j - 1)` and the immediate upward neighbor
  is `(i - 1, j)`, when these cells exist. The number of these neighbors equal to the entry must
  be at most one.
* This reading reproduces all 16 data terms of the entry (brute force for n <= 4 and a row by row
  transfer count for all terms).
* The g.f. is Sum_(n >= 1) a(n) x^n (offset 1, so the constant coefficient is 0). Since the
  denominator has constant term 1, the identity is stated as denominator times series equals
  numerator in the formal power series ring over the integers. The closed form is stated in the
  reals for n > 1, as in the entry, with sqrt as `Real.sqrt`.
* `main` is the conjunction of Barker's two conjectures.
-/

namespace OMA.S_oeis_a208253

open PowerSeries

/-- New values are introduced in row major order: every value smaller than an entry occurs at
an earlier cell in row major order. -/
def NewValuesInOrder {n : ℕ} (A : Fin n → Fin 3 → Fin 3) : Prop :=
  ∀ i j, ∀ v < A i j, ∃ i' j', (i' < i ∨ (i' = i ∧ j' < j)) ∧ A i' j' = v

instance {n : ℕ} (A : Fin n → Fin 3 → Fin 3) : Decidable (NewValuesInOrder A) := by
  unfold NewValuesInOrder; infer_instance

/-- The immediate leftward neighbor `(i, j - 1)` of cell `(i, j)` exists and equals the entry. -/
def LeftEq {n : ℕ} (A : Fin n → Fin 3 → Fin 3) (i : Fin n) (j : Fin 3) : Prop :=
  ∃ j' : Fin 3, j'.val + 1 = j.val ∧ A i j' = A i j

instance {n : ℕ} (A : Fin n → Fin 3 → Fin 3) (i : Fin n) (j : Fin 3) :
    Decidable (LeftEq A i j) := by
  unfold LeftEq; infer_instance

/-- The immediate upward neighbor `(i - 1, j)` of cell `(i, j)` exists and equals the entry. -/
def UpEq {n : ℕ} (A : Fin n → Fin 3 → Fin 3) (i : Fin n) (j : Fin 3) : Prop :=
  ∃ i' : Fin n, i'.val + 1 = i.val ∧ A i' j = A i j

instance {n : ℕ} (A : Fin n → Fin 3 → Fin 3) (i : Fin n) (j : Fin 3) :
    Decidable (UpEq A i j) := by
  unfold UpEq; infer_instance

/-- The number of immediate leftward or upward neighbors of cell `(i, j)` equal to its entry. -/
def numEqNeighbors {n : ℕ} (A : Fin n → Fin 3 → Fin 3) (i : Fin n) (j : Fin 3) : ℕ :=
  (if LeftEq A i j then 1 else 0) + (if UpEq A i j then 1 else 0)

/-- The array introduces new values in row major order and no element equals more than one of
its immediate leftward or upward neighbors. -/
def Valid {n : ℕ} (A : Fin n → Fin 3 → Fin 3) : Prop :=
  NewValuesInOrder A ∧ ∀ i j, numEqNeighbors A i j ≤ 1

instance {n : ℕ} (A : Fin n → Fin 3 → Fin 3) : Decidable (Valid A) := by
  unfold Valid; infer_instance

/-- A208253(n): the number of valid n X 3 arrays over 0..2. -/
def a (n : ℕ) : ℕ :=
  (Finset.univ.filter fun A : Fin n → Fin 3 → Fin 3 => Valid A).card

/-- Barker's conjectures for A208253 (offset 1): the generating function
x(1 - 2x)(5 - 4x) / (1 - 22x + 16x^2), and the closed form for n > 1. -/
theorem main :
    (1 - 22 * X + 16 * X ^ 2) * mk (fun n => if n = 0 then 0 else (a n : ℤ)) =
      (X * (1 - 2 * X) * (5 - 4 * X) : PowerSeries ℤ) ∧
    ∀ n : ℕ, 1 < n → (a n : ℝ) =
      (1 / 32) * Real.sqrt (3 / 35) * ((11 - Real.sqrt 105) ^ n * (-13 + Real.sqrt 105) +
        (11 + Real.sqrt 105) ^ n * (13 + Real.sqrt 105)) := by
  sorry

end OMA.S_oeis_a208253

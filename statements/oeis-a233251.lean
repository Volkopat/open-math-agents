import Mathlib

/-!
# OEIS A233251: Barker's generating function and closed form

Source: https://oeis.org/A233251 (OEIS Foundation, CC BY-SA 4.0).
Credit: @ceejcake

Entry (R. H. Hardin), offset 1: Number of n X 3 0..5 arrays with no element x(i,j) adjacent to
itself or value 5-x(i,j) horizontally or antidiagonally, top left element zero, and 1 appearing
before 2 3 and 4, and 2 appearing before 3 in row major order (unlabelled 6-colorings with no
clashing color pairs).
Data: 3, 104, 4672, 221696, 10620928, 509640704, ...
Formula section: Conjectures from Colin Barker, Oct 10 2018:
G.f.: x*(3 - 64*x) / ((1 - 8*x)*(1 - 48*x)).
a(n) = 8^(n-1) * (6^n+3) / 3.

Formalization notes:
* An n X 3 array over 0..5 is `A : Fin n → Fin 3 → Fin 6`, with `A i j` the entry in row `i`,
  column `j`. Row major order puts cell `(i', j')` before `(i, j)` when `i' < i`, or `i' = i`
  and `j' < j`.
* Two values clash when they are equal or sum to 5. The adjacent pairs are the horizontal pairs
  `(i, j), (i, j + 1)` and the antidiagonal pairs `(i, j + 1), (i + 1, j)`; no adjacent pair may
  clash.
* The top left element `A 0 0` is 0 (when n >= 1).
* "u appearing before v" in row major order: every cell holding v has an earlier cell (in row
  major order) holding u. This is required for u = 1 and v in 2..4, and for u = 2 and v = 3.
* This reading reproduces all 15 data terms of the entry (row by row transfer count).
* The g.f. is Sum_(n >= 1) a(n) x^n (offset 1, so the constant coefficient is 0). Since the
  denominator has constant term 1, the identity is stated as denominator times series equals
  numerator in the formal power series ring over the integers. The closed form is stated in the
  reals for n >= 1 (the offset).
* `main` is the conjunction of Barker's two conjectures.
-/

namespace OMA.S_oeis_a233251

open PowerSeries

/-- Two values clash when they are equal or sum to 5. -/
def Clash (x y : Fin 6) : Prop := x = y ∨ x.val + y.val = 5

instance (x y : Fin 6) : Decidable (Clash x y) := by unfold Clash; infer_instance

/-- No horizontally or antidiagonally adjacent pair of cells holds clashing values. -/
def NoClash {n : ℕ} (A : Fin n → Fin 3 → Fin 6) : Prop :=
  (∀ i, ∀ j j' : Fin 3, j.val + 1 = j'.val → ¬ Clash (A i j) (A i j')) ∧
  (∀ i i' : Fin n, i.val + 1 = i'.val → ∀ j j' : Fin 3, j'.val + 1 = j.val →
    ¬ Clash (A i j) (A i' j'))

instance {n : ℕ} (A : Fin n → Fin 3 → Fin 6) : Decidable (NoClash A) := by
  unfold NoClash; infer_instance

/-- The value `u` occurs at a cell before `(i, j)` in row major order. -/
def Before {n : ℕ} (A : Fin n → Fin 3 → Fin 6) (i : Fin n) (j : Fin 3) (u : Fin 6) : Prop :=
  ∃ i' j', (i' < i ∨ (i' = i ∧ j' < j)) ∧ A i' j' = u

instance {n : ℕ} (A : Fin n → Fin 3 → Fin 6) (i : Fin n) (j : Fin 3) (u : Fin 6) :
    Decidable (Before A i j u) := by
  unfold Before; infer_instance

/-- 1 appears before 2, 3 and 4, and 2 appears before 3, in row major order. -/
def OrderOK {n : ℕ} (A : Fin n → Fin 3 → Fin 6) : Prop :=
  ∀ i j, (2 ≤ (A i j).val → (A i j).val ≤ 4 → Before A i j 1) ∧
    ((A i j).val = 3 → Before A i j 2)

instance {n : ℕ} (A : Fin n → Fin 3 → Fin 6) : Decidable (OrderOK A) := by
  unfold OrderOK; infer_instance

/-- The array is counted: no clashing adjacent pair, top left element zero, and the order
conditions. -/
def Valid {n : ℕ} (A : Fin n → Fin 3 → Fin 6) : Prop :=
  NoClash A ∧ (∀ i, i.val = 0 → A i 0 = 0) ∧ OrderOK A

instance {n : ℕ} (A : Fin n → Fin 3 → Fin 6) : Decidable (Valid A) := by
  unfold Valid; infer_instance

/-- A233251(n): the number of valid n X 3 arrays over 0..5. -/
def a (n : ℕ) : ℕ :=
  (Finset.univ.filter fun A : Fin n → Fin 3 → Fin 6 => Valid A).card

/-- Barker's conjectures for A233251 (offset 1): the generating function
x(3 - 64x) / ((1 - 8x)(1 - 48x)), and the closed form for n >= 1. -/
theorem main :
    (1 - 8 * X) * (1 - 48 * X) * mk (fun n => if n = 0 then 0 else (a n : ℤ)) =
      (X * (3 - 64 * X) : PowerSeries ℤ) ∧
    ∀ n : ℕ, 1 ≤ n → (a n : ℝ) = (8 : ℝ) ^ (n - 1) * (6 ^ n + 3) / 3 := by
  sorry

end OMA.S_oeis_a233251

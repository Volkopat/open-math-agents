import Mathlib

/-!
# OEIS A233196: Barker's generating function and closed form

Source: https://oeis.org/A233196 (OEIS Foundation, CC BY-SA 4.0).
Credit: @ceejcake

Entry (R. H. Hardin), offset 1: Number of n X 2 0..7 arrays with no element x(i,j) adjacent to
itself or value 7-x(i,j) horizontally, antidiagonally or vertically, top left element zero, and
1 appearing before 2 3 4 5 and 6, 2 appearing before 3 4 and 5, and 3 appearing before 4 in row
major order (unlabeled 8-colorings with no clashing color pairs).
Data: 1, 3, 36, 528, 8256, 131328, 2098176, 33558528, ...
Formula section: Conjectures from Colin Barker, Oct 10 2018:
G.f.: x*(1 - 17*x + 40*x^2) / ((1 - 4*x)*(1 - 16*x)).
a(n) = 2^(2*n-7) * (4^n+8) for n>1.

Formalization notes:
* An n X 2 array over 0..7 is `A : Fin n → Fin 2 → Fin 8`, with `A i j` the entry in row `i`,
  column `j`. Row major order puts cell `(i', j')` before `(i, j)` when `i' < i`, or `i' = i`
  and `j' < j`.
* Two values clash when they are equal or sum to 7. The adjacent pairs are the horizontal pairs
  `(i, 0), (i, 1)`, the vertical pairs `(i, j), (i + 1, j)` and the antidiagonal pairs
  `(i, 1), (i + 1, 0)`; no adjacent pair may clash.
* The top left element `A 0 0` is 0 (when n >= 1).
* "u appearing before v" in row major order: every cell holding v has an earlier cell (in row
  major order) holding u. This is required for u = 1 and v in 2..6, for u = 2 and v in 3..5, and
  for u = 3 and v = 4.
* This reading reproduces all 17 data terms of the entry (brute force for n <= 3 and a row by row
  transfer count for all terms).
* The g.f. is Sum_(n >= 1) a(n) x^n (offset 1, so the constant coefficient is 0). Since the
  denominator has constant term 1, the identity is stated as denominator times series equals
  numerator in the formal power series ring over the integers. The closed form is stated in the
  reals for n > 1, with `2^(2n-7)` as an integer power.
* `main` is the conjunction of Barker's two conjectures.
-/

namespace OMA.S_oeis_a233196

open PowerSeries

/-- Two values clash when they are equal or sum to 7. -/
def Clash (x y : Fin 8) : Prop := x = y ∨ x.val + y.val = 7

instance (x y : Fin 8) : Decidable (Clash x y) := by unfold Clash; infer_instance

/-- No horizontally, vertically or antidiagonally adjacent pair of cells holds clashing
values. -/
def NoClash {n : ℕ} (A : Fin n → Fin 2 → Fin 8) : Prop :=
  (∀ i, ¬ Clash (A i 0) (A i 1)) ∧
  (∀ i i' : Fin n, i.val + 1 = i'.val → ∀ j, ¬ Clash (A i j) (A i' j)) ∧
  (∀ i i' : Fin n, i.val + 1 = i'.val → ¬ Clash (A i 1) (A i' 0))

instance {n : ℕ} (A : Fin n → Fin 2 → Fin 8) : Decidable (NoClash A) := by
  unfold NoClash; infer_instance

/-- The value `u` occurs at a cell before `(i, j)` in row major order. -/
def Before {n : ℕ} (A : Fin n → Fin 2 → Fin 8) (i : Fin n) (j : Fin 2) (u : Fin 8) : Prop :=
  ∃ i' j', (i' < i ∨ (i' = i ∧ j' < j)) ∧ A i' j' = u

instance {n : ℕ} (A : Fin n → Fin 2 → Fin 8) (i : Fin n) (j : Fin 2) (u : Fin 8) :
    Decidable (Before A i j u) := by
  unfold Before; infer_instance

/-- 1 appears before 2, 3, 4, 5 and 6, 2 appears before 3, 4 and 5, and 3 appears before 4,
in row major order. -/
def OrderOK {n : ℕ} (A : Fin n → Fin 2 → Fin 8) : Prop :=
  ∀ i j, (2 ≤ (A i j).val → (A i j).val ≤ 6 → Before A i j 1) ∧
    (3 ≤ (A i j).val → (A i j).val ≤ 5 → Before A i j 2) ∧
    ((A i j).val = 4 → Before A i j 3)

instance {n : ℕ} (A : Fin n → Fin 2 → Fin 8) : Decidable (OrderOK A) := by
  unfold OrderOK; infer_instance

/-- The array is counted: no clashing adjacent pair, top left element zero, and the order
conditions. -/
def Valid {n : ℕ} (A : Fin n → Fin 2 → Fin 8) : Prop :=
  NoClash A ∧ (∀ i, i.val = 0 → A i 0 = 0) ∧ OrderOK A

instance {n : ℕ} (A : Fin n → Fin 2 → Fin 8) : Decidable (Valid A) := by
  unfold Valid; infer_instance

/-- A233196(n): the number of valid n X 2 arrays over 0..7. -/
def a (n : ℕ) : ℕ :=
  (Finset.univ.filter fun A : Fin n → Fin 2 → Fin 8 => Valid A).card

/-- Barker's conjectures for A233196 (offset 1): the generating function
x(1 - 17x + 40x^2) / ((1 - 4x)(1 - 16x)), and the closed form for n > 1. -/
theorem main :
    (1 - 4 * X) * (1 - 16 * X) * mk (fun n => if n = 0 then 0 else (a n : ℤ)) =
      (X * (1 - 17 * X + 40 * X ^ 2) : PowerSeries ℤ) ∧
    ∀ n : ℕ, 1 < n → (a n : ℝ) = (2 : ℝ) ^ (2 * (n : ℤ) - 7) * (4 ^ n + 8) := by
  sorry

end OMA.S_oeis_a233196

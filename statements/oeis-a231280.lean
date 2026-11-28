import Mathlib

/-!
# OEIS A231280: Barker's generating function and closed form

Source: https://oeis.org/A231280 (OEIS Foundation, CC BY-SA 4.0).
Credit: @ceejcake

Entry (R. H. Hardin), offset 1: Number of n X 3 0..3 arrays x(i,j) with each element
horizontally or antidiagonally next to at least one element with value (x(i,j)+1) mod 4,
and upper left element zero.
Data: 0, 2, 8, 66, 400, 2722, 17688, 117026, 768800, ...
Formula section: Conjectures from Colin Barker, Sep 28 2018:
G.f.: 2*x^2 / (1 - 4*x - 17*x^2).
a(n) = ((2-sqrt(21))^n*(2+sqrt(21)) + (-2+sqrt(21))*(2+sqrt(21))^n)/(17*sqrt(21)).

Formalization notes:
* An array is a function `A : Fin n → Fin 3 → Fin 4` (row, then column); its entries are the
  values 0, 1, 2, 3.
* The element in row `i'` and column `j'` is horizontally next to the element `(i, j)` when
  `i' = i` and `j' = j ± 1`, and antidiagonally next to it when `(i', j') = (i - 1, j + 1)` or
  `(i', j') = (i + 1, j - 1)` (only positions inside the array count).
  An array is valid when every element `x` has such a neighbour with value `(x + 1) mod 4` and
  the upper left element (row 0, column 0) is 0. This reading reproduces all 21 data terms of
  the entry.
* The g.f. is Sum_(n >= 1) a(n) x^n (offset 1, so the constant coefficient is 0). Since the
  denominator has constant term 1, the identity is stated as denominator times series equals
  numerator in the formal power series ring over the integers. The closed form is stated in the
  reals for n >= 1, with sqrt as `Real.sqrt`.
* `main` is the conjunction of Barker's two conjectures.
-/

namespace OMA.S_oeis_a231280

open PowerSeries

/-- The position `(i', j')` is horizontally or antidiagonally next to the position `(i, j)`:
`(i, j - 1)`, `(i, j + 1)`, `(i - 1, j + 1)` or `(i + 1, j - 1)`. -/
def nextTo (i j i' j' : ℕ) : Prop :=
  (i' = i ∧ (j' + 1 = j ∨ j' = j + 1)) ∨ (i' + 1 = i ∧ j' = j + 1) ∨ (i' = i + 1 ∧ j' + 1 = j)

instance (i j i' j' : ℕ) : Decidable (nextTo i j i' j') := by
  unfold nextTo; infer_instance

/-- An `n × 3` array over `0..3` is valid when each element `x` is horizontally or
antidiagonally next to at least one element with value `(x + 1) mod 4`, and the upper left
element is zero. -/
def valid (n : ℕ) (A : Fin n → Fin 3 → Fin 4) : Prop :=
  (∀ (i : Fin n) (j : Fin 3), ∃ (i' : Fin n) (j' : Fin 3),
    nextTo i.val j.val i'.val j'.val ∧ (A i' j').val = ((A i j).val + 1) % 4) ∧
  (∀ i : Fin n, i.val = 0 → A i 0 = 0)

instance (n : ℕ) : DecidablePred (valid n) := fun A => by
  unfold valid; infer_instance

/-- A231280(n): the number of valid `n × 3` arrays over `0..3`. -/
def a (n : ℕ) : ℕ :=
  (Finset.univ.filter (valid n)).card

/-- Barker's conjectures for A231280 (offset 1): the generating function
2x^2 / (1 - 4x - 17x^2), and the closed form for n >= 1. -/
theorem main :
    (1 - 4 * X - 17 * X ^ 2) * mk (fun n => if n = 0 then 0 else (a n : ℤ)) =
      (2 * X ^ 2 : PowerSeries ℤ) ∧
    ∀ n : ℕ, 1 ≤ n → (a n : ℝ) =
      ((2 - Real.sqrt 21) ^ n * (2 + Real.sqrt 21) + (-2 + Real.sqrt 21) * (2 + Real.sqrt 21) ^ n) /
        (17 * Real.sqrt 21) := by
  sorry

end OMA.S_oeis_a231280

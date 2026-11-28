import Mathlib

/-!
# OEIS A230179: Barker's generating function, closed form and e.g.f.

Source: https://oeis.org/A230179 (OEIS Foundation, CC BY-SA 4.0).
Credit: @ceejcake

Entry (R. H. Hardin), offset 1: Number of n X 3 0..2 arrays x(i,j) with each element
horizontally or antidiagonally next to at least one element with value 2-x(i,j).
Data: 3, 27, 231, 1971, 16815, 143451, 1223799, ...
Formula section: Conjectures from Colin Barker, Sep 21 2018:
G.f.: 3*x / (1 - 9*x + 4*x^2).
a(n) = ((-3)*(2^(-n)*((9-sqrt(65))^n - (9+sqrt(65))^n))) / sqrt(65).
Conjectured e.g.f.: 6*exp(9*x/2)*sinh(sqrt(65)*x/2)/sqrt(65).

Formalization notes:
* An array is a function `A : Fin n → Fin 3 → Fin 3` (row, then column); its entries are the
  values 0, 1, 2.
* The element in row `i'` and column `j'` is horizontally next to the element `(i, j)` when
  `i' = i` and `j' = j ± 1`, and antidiagonally next to it when `(i', j') = (i - 1, j + 1)` or
  `(i', j') = (i + 1, j - 1)` (only positions inside the array count).
  An array is valid when every element `x` has such a neighbour with value `2 - x`, written
  `x' + x = 2` on natural numbers. This reading reproduces all 19 data terms of the entry.
* The g.f. is Sum_(n >= 1) a(n) x^n (offset 1, so the constant coefficient is 0). Since the
  denominator has constant term 1, the identity is stated as denominator times series equals
  numerator in the formal power series ring over the integers. The closed form is stated in the
  reals for n >= 1, with sqrt as `Real.sqrt` and `2^(-n)` as an integer power. The e.g.f. is
  Sum_(n >= 1) a(n) x^n / n! (constant coefficient 0), stated as a convergent sum for every
  real `x`.
* `main` is the conjunction of Barker's three conjectures.
-/

namespace OMA.S_oeis_a230179

open PowerSeries

/-- The position `(i', j')` is horizontally or antidiagonally next to the position `(i, j)`:
`(i, j - 1)`, `(i, j + 1)`, `(i - 1, j + 1)` or `(i + 1, j - 1)`. -/
def nextTo (i j i' j' : ℕ) : Prop :=
  (i' = i ∧ (j' + 1 = j ∨ j' = j + 1)) ∨ (i' + 1 = i ∧ j' = j + 1) ∨ (i' = i + 1 ∧ j' + 1 = j)

instance (i j i' j' : ℕ) : Decidable (nextTo i j i' j') := by
  unfold nextTo; infer_instance

/-- An `n × 3` array over `0..2` is valid when each element `x` is horizontally or
antidiagonally next to at least one element with value `2 - x`. -/
def valid (n : ℕ) (A : Fin n → Fin 3 → Fin 3) : Prop :=
  ∀ (i : Fin n) (j : Fin 3), ∃ (i' : Fin n) (j' : Fin 3),
    nextTo i.val j.val i'.val j'.val ∧ (A i' j').val + (A i j).val = 2

instance (n : ℕ) : DecidablePred (valid n) := fun A => by
  unfold valid; infer_instance

/-- A230179(n): the number of valid `n × 3` arrays over `0..2`. -/
def a (n : ℕ) : ℕ :=
  (Finset.univ.filter (valid n)).card

/-- Barker's conjectures for A230179 (offset 1): the generating function
3x / (1 - 9x + 4x^2), the closed form for n >= 1, and the exponential generating function
6 exp(9x/2) sinh(sqrt(65) x/2) / sqrt(65). -/
theorem main :
    (1 - 9 * X + 4 * X ^ 2) * mk (fun n => if n = 0 then 0 else (a n : ℤ)) =
      (3 * X : PowerSeries ℤ) ∧
    (∀ n : ℕ, 1 ≤ n → (a n : ℝ) =
      ((-3) * ((2 : ℝ) ^ (-(n : ℤ)) * ((9 - Real.sqrt 65) ^ n - (9 + Real.sqrt 65) ^ n))) /
        Real.sqrt 65) ∧
    ∀ x : ℝ, HasSum (fun n : ℕ => (if n = 0 then 0 else (a n : ℝ)) * x ^ n / (n.factorial : ℝ))
      (6 * Real.exp (9 * x / 2) * Real.sinh (Real.sqrt 65 * x / 2) / Real.sqrt 65) := by
  sorry

end OMA.S_oeis_a230179

import Mathlib

/-!
# OEIS A253029: Barker's generating function and closed form

Source: https://oeis.org/A253029 (OEIS Foundation, CC BY-SA 4.0).
Credit: @ceejcake

Entry (R. H. Hardin), offset 1: Number of (n+2) X (1+2) 0..2 arrays with every consecutive
three elements in every row and column having exactly two distinct values, and new values 0
upwards introduced in row major order.
Data: 297, 1647, 9126, 50571, 280233, 1552878, 8605089, ...
Formula section: Conjectures from Colin Barker, Dec 08 2018:
G.f.: 27*x*(11 + 6*x) / (1 - 5*x - 3*x^2).
a(n) = (27*2^(-n)*((5-sqrt(37))^n*(-6+sqrt(37)) + (5+sqrt(37))^n*(6+sqrt(37)))) / sqrt(37).

Formalization notes:
* An array is a function `A : Fin (n + 2) → Fin 3 → Fin 3` (row, then column); its entries are
  the values 0, 1, 2.
* Rows have exactly three elements, so the only three consecutive elements of row `i` are
  `A i 0, A i 1, A i 2`; the three consecutive elements of column `j` are
  `A i j, A (i + 1) j, A (i + 2) j` for `i < n`. "Exactly two distinct values" is the
  cardinality of the set of the three values being 2.
* "New values 0 upwards introduced in row major order": every element with value `v ≥ 1` is
  preceded in row major order (an earlier row, or the same row and an earlier column) by an
  element with value `v - 1`. In particular the first element is 0.
  This reading reproduces all 18 data terms of the entry.
* The g.f. is Sum_(n >= 1) a(n) x^n (offset 1, so the constant coefficient is 0). Since the
  denominator has constant term 1, the identity is stated as denominator times series equals
  numerator in the formal power series ring over the integers. The closed form is stated in the
  reals for n >= 1, with sqrt as `Real.sqrt` and `2^(-n)` as an integer power.
* `main` is the conjunction of Barker's two conjectures.
-/

namespace OMA.S_oeis_a253029

open PowerSeries

/-- An `(n + 2) × 3` array over `0..2` is valid when every three consecutive elements of every
row and of every column take exactly two distinct values, and new values are introduced in
row major order starting from 0. -/
def valid (n : ℕ) (A : Fin (n + 2) → Fin 3 → Fin 3) : Prop :=
  (∀ i : Fin (n + 2), ({A i 0, A i 1, A i 2} : Finset (Fin 3)).card = 2) ∧
  (∀ (i : Fin n) (j : Fin 3),
    ({A ⟨i.val, by omega⟩ j, A ⟨i.val + 1, by omega⟩ j, A ⟨i.val + 2, by omega⟩ j} :
      Finset (Fin 3)).card = 2) ∧
  (∀ (i : Fin (n + 2)) (j : Fin 3), 1 ≤ (A i j).val →
    ∃ (i' : Fin (n + 2)) (j' : Fin 3), (i'.val < i.val ∨ (i' = i ∧ j'.val < j.val)) ∧
      (A i' j').val + 1 = (A i j).val)

instance (n : ℕ) : DecidablePred (valid n) := fun A => by
  unfold valid; infer_instance

/-- A253029(n): the number of valid `(n + 2) × 3` arrays over `0..2`. -/
def a (n : ℕ) : ℕ :=
  (Finset.univ.filter (valid n)).card

/-- Barker's conjectures for A253029 (offset 1): the generating function
27x(11 + 6x) / (1 - 5x - 3x^2), and the closed form for n >= 1. -/
theorem main :
    (1 - 5 * X - 3 * X ^ 2) * mk (fun n => if n = 0 then 0 else (a n : ℤ)) =
      (27 * X * (11 + 6 * X) : PowerSeries ℤ) ∧
    ∀ n : ℕ, 1 ≤ n → (a n : ℝ) =
      (27 * ((2 : ℝ) ^ (-(n : ℤ)) * ((5 - Real.sqrt 37) ^ n * (-6 + Real.sqrt 37) +
        (5 + Real.sqrt 37) ^ n * (6 + Real.sqrt 37)))) / Real.sqrt 37 := by
  sorry

end OMA.S_oeis_a253029

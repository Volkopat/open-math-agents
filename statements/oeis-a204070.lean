import Mathlib

/-!
# OEIS A204070: Barker's generating function and closed form

Source: https://oeis.org/A204070 (OEIS Foundation, CC BY-SA 4.0).
Credit: @ceejcake

Entry (R. H. Hardin), offset 1: Number of (n+1) X 3 0..2 arrays with every 2 X 2 subblock having
equal diagonal elements or equal antidiagonal elements, and new values 0..2 introduced in row
major order.
Data: 38, 329, 2882, 25277, 221726, 1944977, 17061338, ...
Formula section: Conjectures from Colin Barker, Jun 06 2018:
G.f.: x*(38 - 51*x + 10*x^2) / ((1 - x)*(1 - 9*x + 2*x^2)).
a(n) = 1/2 + (2^(-2-n)*(3*(9+sqrt(73))^n*(23+3*sqrt(73)) + (9-sqrt(73))^n*(-69+9*sqrt(73))))
  / sqrt(73).

Formalization notes:
* An array is `A : Fin (n + 1) → Fin 3 → Fin 3`; `A i j` is the element in row `i`, column `j`.
* The 2 X 2 subblock at rows `i, i+1` and columns `j, j+1` is `a b / c d` with `a = A i j`,
  `b = A i (j+1)`, `c = A (i+1) j`, `d = A (i+1) (j+1)`; it must satisfy `a = d` (equal diagonal
  elements) or `b = c` (equal antidiagonal elements).
* New values 0..2 are introduced in row major order: every value smaller than an element occurs
  at an earlier position (row-major index `3 * i + j`).
* This reading reproduces all 18 data terms of the entry (brute force for n <= 3 and a transfer
  count for all terms).
* The g.f. is Sum_(n >= 1) a(n) x^n (offset 1, so the constant coefficient is 0), stated as
  denominator times series equals numerator in the formal power series ring over the integers.
  The closed form is stated in the reals for n >= 1, with sqrt as `Real.sqrt`.
-/

namespace OMA.S_oeis_a204070

open PowerSeries

/-- Every 2 X 2 subblock has equal diagonal elements or equal antidiagonal elements. -/
def SubblockCondition {n : ℕ} (A : Fin (n + 1) → Fin 3 → Fin 3) : Prop :=
  ∀ (i : Fin n) (j : Fin 2), A i.castSucc j.castSucc = A i.succ j.succ ∨
    A i.castSucc j.succ = A i.succ j.castSucc

/-- New values are introduced in row major order: every value smaller than an element of the
array occurs at an earlier position. -/
def NewValuesInOrder {n : ℕ} (A : Fin (n + 1) → Fin 3 → Fin 3) : Prop :=
  ∀ (i : Fin (n + 1)) (j : Fin 3) (w : Fin 3), w < A i j →
    ∃ (i' : Fin (n + 1)) (j' : Fin 3), 3 * (i' : ℕ) + j' < 3 * (i : ℕ) + j ∧ A i' j' = w

/-- `SubblockCondition` is decidable (all quantifiers range over finite types). -/
instance {n : ℕ} : DecidablePred (SubblockCondition (n := n)) := fun A => by
  unfold SubblockCondition; infer_instance

/-- `NewValuesInOrder` is decidable (all quantifiers range over finite types). -/
instance {n : ℕ} : DecidablePred (NewValuesInOrder (n := n)) := fun A => by
  unfold NewValuesInOrder; infer_instance

/-- A204070(n): the number of (n+1) X 3 arrays with entries 0..2 in which every 2 X 2 subblock
has equal diagonal or equal antidiagonal elements, with new values introduced in row major
order. -/
def a (n : ℕ) : ℕ :=
  (Finset.univ.filter fun A : Fin (n + 1) → Fin 3 → Fin 3 =>
    SubblockCondition A ∧ NewValuesInOrder A).card

/-- Barker's conjectures for A204070 (offset 1): the generating function
x(38 - 51x + 10x^2) / ((1 - x)(1 - 9x + 2x^2)), and the closed form for n >= 1. -/
theorem main :
    (1 - X) * (1 - 9 * X + 2 * X ^ 2) * mk (fun n => if n = 0 then 0 else (a n : ℤ)) =
      (X * (38 - 51 * X + 10 * X ^ 2) : PowerSeries ℤ) ∧
    ∀ n : ℕ, 1 ≤ n → (a n : ℝ) =
      1 / 2 + (2 ^ (-2 - (n : ℤ)) * (3 * (9 + Real.sqrt 73) ^ n * (23 + 3 * Real.sqrt 73) +
        (9 - Real.sqrt 73) ^ n * (-69 + 9 * Real.sqrt 73))) / Real.sqrt 73 := by
  sorry

end OMA.S_oeis_a204070

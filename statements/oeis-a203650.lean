import Mathlib

/-!
# OEIS A203650: Barker's generating function and closed form

Source: https://oeis.org/A203650 (OEIS Foundation, CC BY-SA 4.0).
Credit: @ceejcake

Entry (R. H. Hardin), offset 1: 1/25 the number of (n+1) X 3 0..4 arrays with every 2 X 2
subblock having equal diagonal elements or equal antidiagonal elements.
Data: 81, 1517, 28057, 519445, 9616161, 178019197, ...
Formula section: Conjectures from Colin Barker, Jun 04 2018:
G.f.: x*(81 + 140*x) / (1 - 17*x - 28*x^2).
a(n) = (2^(-1-n)*((17-sqrt(401))^n*(-77+5*sqrt(401)) + (17+sqrt(401))^n*(77+5*sqrt(401))))
  / sqrt(401).

Formalization notes:
* An array is `A : Fin (n + 1) → Fin 3 → Fin 5`; `A i j` is the element in row `i`, column `j`.
* The 2 X 2 subblock at rows `i, i+1` and columns `j, j+1` is `a b / c d` with `a = A i j`,
  `b = A i (j+1)`, `c = A (i+1) j`, `d = A (i+1) (j+1)`; it must satisfy `a = d` (equal diagonal
  elements) or `b = c` (equal antidiagonal elements).
* `a n` is the number of such arrays divided by 25, as a rational number. This reading
  reproduces all 15 data terms of the entry (brute force for n = 1 and a transfer count for all
  terms; every count is divisible by 25).
* The g.f. is Sum_(n >= 1) a(n) x^n (offset 1, so the constant coefficient is 0), stated as
  denominator times series equals numerator in the formal power series ring over the rationals.
  The closed form is stated in the reals for n >= 1, with sqrt as `Real.sqrt`.
-/

namespace OMA.S_oeis_a203650

open PowerSeries

/-- Every 2 X 2 subblock has equal diagonal elements or equal antidiagonal elements. -/
def SubblockCondition {n : ℕ} (A : Fin (n + 1) → Fin 3 → Fin 5) : Prop :=
  ∀ (i : Fin n) (j : Fin 2), A i.castSucc j.castSucc = A i.succ j.succ ∨
    A i.castSucc j.succ = A i.succ j.castSucc

/-- `SubblockCondition` is decidable (all quantifiers range over finite types). -/
instance {n : ℕ} : DecidablePred (SubblockCondition (n := n)) := fun A => by
  unfold SubblockCondition; infer_instance

/-- A203650(n): 1/25 of the number of (n+1) X 3 arrays with entries 0..4 in which every 2 X 2
subblock has equal diagonal elements or equal antidiagonal elements. -/
def a (n : ℕ) : ℚ :=
  ((Finset.univ.filter fun A : Fin (n + 1) → Fin 3 → Fin 5 => SubblockCondition A).card : ℚ) / 25

/-- Barker's conjectures for A203650 (offset 1): the generating function
x(81 + 140x) / (1 - 17x - 28x^2), and the closed form for n >= 1. -/
theorem main :
    (1 - 17 * X - 28 * X ^ 2) * mk (fun n => if n = 0 then 0 else a n) =
      (X * (81 + 140 * X) : PowerSeries ℚ) ∧
    ∀ n : ℕ, 1 ≤ n → (a n : ℝ) =
      (2 ^ (-1 - (n : ℤ)) * ((17 - Real.sqrt 401) ^ n * (-77 + 5 * Real.sqrt 401) +
        (17 + Real.sqrt 401) ^ n * (77 + 5 * Real.sqrt 401))) / Real.sqrt 401 := by
  sorry

end OMA.S_oeis_a203650

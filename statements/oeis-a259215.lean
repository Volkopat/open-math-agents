import Mathlib

/-!
# OEIS A259215: Barker's generating function and closed form

Source: https://oeis.org/A259215 (OEIS Foundation, CC BY-SA 4.0).

Entry (R. H. Hardin), offset 1: Number of (n+1) X (1+1) 0..1 arrays with each 2 X 2 subblock
having clockwise pattern 0000 0011 or 0101. Data: 7, 13, 24, 45, 85, 162, 311, 601, ...
Formula section: Conjectures from Colin Barker, Dec 24 2018:
G.f.: x*(7 - 8*x - 8*x^2) / ((1 - 2*x)*(1 - x - x^2)).
a(n) = 2^(1+n) + (2^(-n)*((1-sqrt(5))^n*(-2+sqrt(5)) + (1+sqrt(5))^n*(2+sqrt(5)))) / sqrt(5).

Formalization notes:
* An array is a function `A : Fin (n + 1) → Fin 2 → Fin 2` (row, then column).
* The 2 X 2 subblock on rows `i, i + 1` read clockwise from its top-left corner is
  `A i 0, A i 1, A (i + 1) 1, A (i + 1) 0`. Its clockwise pattern is one of 0000, 0011, 0101
  when this word is a cyclic rotation of one of those three words (a(1) = 7 = 1 + 4 + 2).
  This reading reproduces all 33 data terms of the entry.
* The g.f. is Sum_(n >= 1) a(n) x^n (offset 1, so the constant coefficient is 0). Since the
  denominator has constant term 1, the identity is stated as denominator times series equals
  numerator in the formal power series ring over the integers. The closed form is stated in the
  reals for n >= 1, with sqrt as `Real.sqrt` and 2^(-n) as an integer power.
* `main` is the conjunction of Barker's two conjectures.
-/

namespace OMA.S_oeis_a259215

open PowerSeries

/-- A word `w` of four bits is a clockwise pattern 0000, 0011 or 0101 when it is a rotation of
one of these words. -/
def goodPattern (w : List (Fin 2)) : Prop :=
  ∃ k : Fin 4, ∃ p ∈ [[0, 0, 0, 0], [0, 0, 1, 1], [0, 1, 0, 1]], w = p.rotate k

instance (w : List (Fin 2)) : Decidable (goodPattern w) := by
  unfold goodPattern; infer_instance

/-- An `(n + 1) × 2` binary array is valid when every `2 × 2` subblock, read clockwise from its
top-left corner, has one of the clockwise patterns 0000, 0011, 0101. -/
def valid (n : ℕ) (A : Fin (n + 1) → Fin 2 → Fin 2) : Prop :=
  ∀ i : Fin n, goodPattern [A i.castSucc 0, A i.castSucc 1, A i.succ 1, A i.succ 0]

instance (n : ℕ) : DecidablePred (valid n) := fun A => by
  unfold valid; infer_instance

/-- A259215(n): the number of `(n + 1) × 2` binary arrays in which every `2 × 2` subblock has
clockwise pattern 0000, 0011 or 0101. -/
def a (n : ℕ) : ℕ :=
  (Finset.univ.filter (valid n)).card

/-- Barker's conjectures for A259215 (offset 1): the generating function
x(7 - 8x - 8x^2) / ((1 - 2x)(1 - x - x^2)), and the closed form for n >= 1. -/
theorem main :
    (1 - 2 * X) * (1 - X - X ^ 2) * mk (fun n => if n = 0 then 0 else (a n : ℤ)) =
      (X * (7 - 8 * X - 8 * X ^ 2) : PowerSeries ℤ) ∧
    ∀ n : ℕ, 1 ≤ n → (a n : ℝ) =
      2 ^ (1 + n) + ((2 : ℝ) ^ (-(n : ℤ)) * ((1 - Real.sqrt 5) ^ n * (-2 + Real.sqrt 5) +
        (1 + Real.sqrt 5) ^ n * (2 + Real.sqrt 5))) / Real.sqrt 5 := by
  sorry

end OMA.S_oeis_a259215

import Mathlib

/-!
# OEIS A269461: Barker's generating function and closed form

Source: https://oeis.org/A269461 (OEIS Foundation, CC BY-SA 4.0).
Credit: @ceejcake

Entry (R. H. Hardin), offset 1: Number of length-n 0..2 arrays with no repeated value equal to
the previous repeated value. Data: 3, 9, 24, 66, 174, 462, 1206, ...
Formula section: Conjectures from Colin Barker, Mar 21 2018:
G.f.: 3*x*(1 - 3*x^2) / ((1 - 2*x)*(1 - x - 4*x^2)).
a(n) = 2^(-4-n)*(-51*4^(1+n) + (255-57*sqrt(17))*(1-sqrt(17))^n
  + 3*(1+sqrt(17))^n*(85+19*sqrt(17))) / 17.

Formalization notes:
* An array is a function `Fin n → Fin 3`, read from its first element as `List.ofFn x`.
* A repeated value is an element equal to the element before it (an adjacent equal pair
  x(i) = x(i-1)); its value is that element. Reading the repeats in order, each repeated value
  must differ from the previous repeated value. The first repeat is unconstrained.
* `ok r p l` scans the rest `l` of the array, where `p` is the element before it and `r` is the
  value at the last repeat so far (`none` before the first repeat). `valid` starts the scan at
  the first element. This reading reproduces all 27 data terms of the entry (brute force for
  n <= 7, and a transfer count for all terms).
* The g.f. is Sum_(n >= 1) a(n) x^n (offset 1, so the constant coefficient is 0). Since the
  denominator has constant term 1, the identity is stated as denominator times series equals
  numerator in the formal power series ring over the integers. The closed form is stated in the
  reals for n >= 1, with sqrt as `Real.sqrt` and 2^(-4-n) as an integer power.
* `main` is the conjunction of Barker's two conjectures.
-/

namespace OMA.S_oeis_a269461

open PowerSeries

/-- Scanning an array from left to right. `r` is the value at the last repeat so far (`none`
before the first repeat) and `p` is the element before the rest of the array. An element equal
to the one before it is a repeat, and its value must differ from the previous repeated value. -/
def ok {α : Type} [DecidableEq α] : Option α → α → List α → Bool
  | _, _, [] => true
  | r, p, c :: l => if c = p then decide (r ≠ some c) && ok (some c) c l else ok r c l

/-- An array passes when the scan from its first element passes. -/
def valid {α : Type} [DecidableEq α] : List α → Bool
  | [] => true
  | c :: l => ok none c l

/-- A269461(n): the number of length-n arrays with entries 0..2 in which no repeated value
equals the previous repeated value. -/
def a (n : ℕ) : ℕ :=
  (Finset.univ.filter fun x : Fin n → Fin 3 => valid (List.ofFn x) = true).card

/-- Barker's conjectures for A269461 (offset 1): the generating function
3x(1 - 3x^2) / ((1 - 2x)(1 - x - 4x^2)), and the closed form for n >= 1. -/
theorem main :
    (1 - 2 * X) * (1 - X - 4 * X ^ 2) * mk (fun n => if n = 0 then 0 else (a n : ℤ)) =
      (3 * X * (1 - 3 * X ^ 2) : PowerSeries ℤ) ∧
    ∀ n : ℕ, 1 ≤ n → (a n : ℝ) =
      (2 : ℝ) ^ (-4 - (n : ℤ)) * (-51 * 4 ^ (1 + n) +
        (255 - 57 * Real.sqrt 17) * (1 - Real.sqrt 17) ^ n +
        3 * (1 + Real.sqrt 17) ^ n * (85 + 19 * Real.sqrt 17)) / 17 := by
  sorry

end OMA.S_oeis_a269461

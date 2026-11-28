import Mathlib

/-!
# OEIS A268943: Barker's generating function and closed form

Source: https://oeis.org/A268943 (OEIS Foundation, CC BY-SA 4.0).
Credit: @ceejcake

Entry (R. H. Hardin), offset 1: Number of length-n 0..7 arrays with no repeated value unequal to
the previous repeated value plus one mod 7+1. Data: 8, 64, 504, 3928, 30344, 232696, ...
Formula section: Conjectures from Colin Barker, Jan 17 2019:
G.f.: 8*x*(1 - 5*x - 7*x^2) / ((1 - 7*x)*(1 - 6*x - 8*x^2)).
a(n) = (-272*7^n + (153-37*sqrt(17))*(3-sqrt(17))^n + (3+sqrt(17))^n*(153+37*sqrt(17))) / 34.

Formalization notes:
* An array is a function `Fin n → Fin 8`, read from its first element as `List.ofFn x`.
  Addition in `Fin 8` is addition mod 8 = 7+1.
* A repeated value is an element equal to the element before it (an adjacent equal pair
  x(i) = x(i-1)); its value is that element. Reading the repeats in order, each repeated value
  must equal the previous repeated value plus one mod 8. The first repeat is unconstrained.
* `ok r p l` scans the rest `l` of the array, where `p` is the element before it and `r` is the
  value at the last repeat so far (`none` before the first repeat). `valid` starts the scan at
  the first element. This reading reproduces all 19 data terms of the entry (brute force for
  n <= 6, and a transfer count for all terms).
* The g.f. is Sum_(n >= 1) a(n) x^n (offset 1, so the constant coefficient is 0). Since the
  denominator has constant term 1, the identity is stated as denominator times series equals
  numerator in the formal power series ring over the integers. The closed form is stated in the
  reals for n >= 1, with sqrt as `Real.sqrt`.
* `main` is the conjunction of Barker's two conjectures.
-/

namespace OMA.S_oeis_a268943

open PowerSeries

/-- Scanning an array from left to right. `r` is the value at the last repeat so far (`none`
before the first repeat) and `p` is the element before the rest of the array. An element equal
to the one before it is a repeat, and its value must be the previous repeated value plus one
mod 8. -/
def ok : Option (Fin 8) → Fin 8 → List (Fin 8) → Bool
  | _, _, [] => true
  | r, p, c :: l =>
    if c = p then (r.all fun v => decide (c = v + 1)) && ok (some c) c l else ok r c l

/-- An array passes when the scan from its first element passes. -/
def valid : List (Fin 8) → Bool
  | [] => true
  | c :: l => ok none c l

/-- A268943(n): the number of length-n arrays with entries 0..7 in which every repeated value
after the first equals the previous repeated value plus one mod 8. -/
def a (n : ℕ) : ℕ :=
  (Finset.univ.filter fun x : Fin n → Fin 8 => valid (List.ofFn x) = true).card

/-- Barker's conjectures for A268943 (offset 1): the generating function
8x(1 - 5x - 7x^2) / ((1 - 7x)(1 - 6x - 8x^2)), and the closed form for n >= 1. -/
theorem main :
    (1 - 7 * X) * (1 - 6 * X - 8 * X ^ 2) * mk (fun n => if n = 0 then 0 else (a n : ℤ)) =
      (8 * X * (1 - 5 * X - 7 * X ^ 2) : PowerSeries ℤ) ∧
    ∀ n : ℕ, 1 ≤ n → (a n : ℝ) =
      (-272 * 7 ^ n + (153 - 37 * Real.sqrt 17) * (3 - Real.sqrt 17) ^ n +
        (3 + Real.sqrt 17) ^ n * (153 + 37 * Real.sqrt 17)) / 34 := by
  sorry

end OMA.S_oeis_a268943

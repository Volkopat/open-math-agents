import Mathlib

/-!
# OEIS A268939: Barker's generating function and closed form

Source: https://oeis.org/A268939 (OEIS Foundation, CC BY-SA 4.0).
Credit: @ceejcake

Entry (R. H. Hardin), offset 1: Number of length-n 0..3 arrays with no repeated value unequal to
the previous repeated value plus one mod 3+1. Data: 4, 16, 60, 220, 788, 2780, ...
Formula section: Conjectures from Colin Barker, Jan 16 2019:
G.f.: 4*x*(1 - x - 3*x^2) / ((1 - 3*x)*(1 - 2*x - 4*x^2)).
a(n) = (-40*3^n + (25-11*sqrt(5))*(1-sqrt(5))^n + (1+sqrt(5))^n*(25+11*sqrt(5))) / 10.

Formalization notes:
* An array is a function `Fin n → Fin 4`, read from its first element as `List.ofFn x`.
  Addition in `Fin 4` is addition mod 4 = 3+1.
* A repeated value is an element equal to the element before it (an adjacent equal pair
  x(i) = x(i-1)); its value is that element. Reading the repeats in order, each repeated value
  must equal the previous repeated value plus one mod 4. The first repeat is unconstrained.
* `ok r p l` scans the rest `l` of the array, where `p` is the element before it and `r` is the
  value at the last repeat so far (`none` before the first repeat). `valid` starts the scan at
  the first element. This reading reproduces all 24 data terms of the entry (brute force for
  n <= 8, and a transfer count for all terms).
* The g.f. is Sum_(n >= 1) a(n) x^n (offset 1, so the constant coefficient is 0). Since the
  denominator has constant term 1, the identity is stated as denominator times series equals
  numerator in the formal power series ring over the integers. The closed form is stated in the
  reals for n >= 1, with sqrt as `Real.sqrt`.
* `main` is the conjunction of Barker's two conjectures.
-/

namespace OMA.S_oeis_a268939

open PowerSeries

/-- Scanning an array from left to right. `r` is the value at the last repeat so far (`none`
before the first repeat) and `p` is the element before the rest of the array. An element equal
to the one before it is a repeat, and its value must be the previous repeated value plus one
mod 4. -/
def ok : Option (Fin 4) → Fin 4 → List (Fin 4) → Bool
  | _, _, [] => true
  | r, p, c :: l =>
    if c = p then (r.all fun v => decide (c = v + 1)) && ok (some c) c l else ok r c l

/-- An array passes when the scan from its first element passes. -/
def valid : List (Fin 4) → Bool
  | [] => true
  | c :: l => ok none c l

/-- A268939(n): the number of length-n arrays with entries 0..3 in which every repeated value
after the first equals the previous repeated value plus one mod 4. -/
def a (n : ℕ) : ℕ :=
  (Finset.univ.filter fun x : Fin n → Fin 4 => valid (List.ofFn x) = true).card

/-- Barker's conjectures for A268939 (offset 1): the generating function
4x(1 - x - 3x^2) / ((1 - 3x)(1 - 2x - 4x^2)), and the closed form for n >= 1. -/
theorem main :
    (1 - 3 * X) * (1 - 2 * X - 4 * X ^ 2) * mk (fun n => if n = 0 then 0 else (a n : ℤ)) =
      (4 * X * (1 - X - 3 * X ^ 2) : PowerSeries ℤ) ∧
    ∀ n : ℕ, 1 ≤ n → (a n : ℝ) =
      (-40 * 3 ^ n + (25 - 11 * Real.sqrt 5) * (1 - Real.sqrt 5) ^ n +
        (1 + Real.sqrt 5) ^ n * (25 + 11 * Real.sqrt 5)) / 10 := by
  sorry

end OMA.S_oeis_a268939

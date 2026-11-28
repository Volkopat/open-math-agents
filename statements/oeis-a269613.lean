import Mathlib

/-!
# OEIS A269613: Barker's generating function and closed form

Source: https://oeis.org/A269613 (OEIS Foundation, CC BY-SA 4.0).
Credit: @ceejcake

Entry (R. H. Hardin), offset 1: Number of length-n 0..2 arrays with no repeated value differing
from the previous repeated value by other than plus two, zero or minus 1.
Data: 3, 9, 27, 78, 222, 624, 1740, ...
Formula section: Conjectures from Colin Barker, Mar 21 2018:
G.f.: 3*x*(1 - x - x^2) / ((1 - 2*x)*(1 - 2*x - 2*x^2)).
a(n) = (-3*2^n + (3-2*sqrt(3))*(1-sqrt(3))^n + (1+sqrt(3))^n*(3+2*sqrt(3))) / 4.

Formalization notes:
* An array is a function `Fin n → Fin 3`, read from its first element as `List.ofFn x`.
* A repeated value is an element equal to the element before it (an adjacent equal pair
  x(i) = x(i-1)); its value is that element. Reading the repeats in order, each repeated value
  minus the previous repeated value (as integers) must be 2, 0 or -1. The first repeat is
  unconstrained. In particular a repeat may equal the previous repeat (difference zero), so for
  example the array 0, 0, 0 is counted, as the data term a(3) = 27 requires.
* `ok r p l` scans the rest `l` of the array, where `p` is the element before it and `r` is the
  value at the last repeat so far (`none` before the first repeat). `valid` starts the scan at
  the first element. This reading reproduces all 26 data terms of the entry (brute force for
  n <= 11, and a transfer count for all terms).
* The g.f. is Sum_(n >= 1) a(n) x^n (offset 1, so the constant coefficient is 0). Since the
  denominator has constant term 1, the identity is stated as denominator times series equals
  numerator in the formal power series ring over the integers. The closed form is stated in the
  reals for n >= 1, with sqrt as `Real.sqrt`.
* `main` is the conjunction of Barker's two conjectures.
-/

namespace OMA.S_oeis_a269613

open PowerSeries

/-- Scanning an array from left to right. `r` is the value at the last repeat so far (`none`
before the first repeat) and `p` is the element before the rest of the array. An element equal
to the one before it is a repeat, and its value minus the previous repeated value must be
2, 0 or -1. -/
def ok : Option (Fin 3) → Fin 3 → List (Fin 3) → Bool
  | _, _, [] => true
  | r, p, c :: l =>
    if c = p then
      (r.all fun v => decide ((c.val : ℤ) - v.val = 2 ∨ (c.val : ℤ) - v.val = 0 ∨
        (c.val : ℤ) - v.val = -1)) && ok (some c) c l
    else ok r c l

/-- An array passes when the scan from its first element passes. -/
def valid : List (Fin 3) → Bool
  | [] => true
  | c :: l => ok none c l

/-- A269613(n): the number of length-n arrays with entries 0..2 in which every repeated value
after the first differs from the previous repeated value by plus two, zero or minus one. -/
def a (n : ℕ) : ℕ :=
  (Finset.univ.filter fun x : Fin n → Fin 3 => valid (List.ofFn x) = true).card

/-- Barker's conjectures for A269613 (offset 1): the generating function
3x(1 - x - x^2) / ((1 - 2x)(1 - 2x - 2x^2)), and the closed form for n >= 1. -/
theorem main :
    (1 - 2 * X) * (1 - 2 * X - 2 * X ^ 2) * mk (fun n => if n = 0 then 0 else (a n : ℤ)) =
      (3 * X * (1 - X - X ^ 2) : PowerSeries ℤ) ∧
    ∀ n : ℕ, 1 ≤ n → (a n : ℝ) =
      (-3 * 2 ^ n + (3 - 2 * Real.sqrt 3) * (1 - Real.sqrt 3) ^ n +
        (1 + Real.sqrt 3) ^ n * (3 + 2 * Real.sqrt 3)) / 4 := by
  sorry

end OMA.S_oeis_a269613

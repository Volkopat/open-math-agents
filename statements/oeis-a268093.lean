import Mathlib

/-!
# OEIS A268093: Barker's generating function and closed form

Source: https://oeis.org/A268093 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry (R. H. Hardin, Jan 26 2016), offset 1: Number of 1 X n 0..2 arrays with every repeated
value in every row not one larger and in every column one larger mod 3 than the previous
repeated value, and upper left element zero. Data: 1, 3, 9, 26, 74, 208, 580, ... Formula
section: Conjectures from Colin Barker, Jan 11 2019:
G.f.: x*(1 - x - x^2) / ((1 - 2*x)*(1 - 2*x - 2*x^2)).
a(n) = (-3*2^n + (3-2*sqrt(3))*(1-sqrt(3))^n + (1+sqrt(3))^n*(3+2*sqrt(3))) / 12.

Formalization notes:
* A 1 X n array has columns of one element, so the column condition is empty and only its single
  row, read from the left, is constrained. A repeated value is an element equal to the element to
  its left; each repeated value after the first must not be one larger mod 3 than the previous
  repeated value of the row. Reading one larger in the integers instead gives 75 for n = 5, not
  the entry's 74, so mod 3 applies to the row condition too. The array is a function
  `Fin n → Fin 3` and its row is `List.ofFn x`.
* `ok r p l` scans the rest `l` of the row, where `p` is the element to its left and `r` is the
  value of the last repeat so far (`none` before the first); `valid` adds that the upper left
  element is 0. This reading reproduces the first nine terms of the entry's data by brute force.
* The g.f. is the formal power series Sum_{n >= 1} a(n) x^n over the rationals (offset 1, so the
  constant coefficient is 0), and the claim is that it equals the numerator times the inverse of
  the denominator, whose constant term is 1. The closed form is stated in the reals for the terms
  of the sequence, n >= 1, with sqrt as `Real.sqrt`.
* `main` is the conjunction of Barker's two conjectures.
* Controls (proved in the proof file): a(1..14) = 1, 3, 9, 26, 74, 208, 580, 1608, 4440, 12224,
  33584, 92128, 252448, 691200, the entry's data, and a(4) = 26 by direct enumeration of the 81
  arrays.
-/

namespace OMA.S_oeis_a268093

open PowerSeries

/-- Scanning a row from the left: `r` is the value at the last repeat so far (`none` before the
first repeat) and `p` is the element to the left of the rest of the row. An element equal to the
one to its left is a repeat, and its value must not be one larger mod 3 than the value at the
previous repeat. -/
def ok : Option (Fin 3) → Fin 3 → List (Fin 3) → Bool
  | _, _, [] => true
  | r, p, c :: l =>
    if c = p then (r.all fun v => decide (c ≠ v + 1)) && ok (some c) c l else ok r c l

/-- A 1 X n array, read as its single row from the left: the upper left element is 0 and the row
passes the scan. -/
def valid : List (Fin 3) → Bool
  | [] => true
  | c :: l => decide (c = 0) && ok none c l

/-- A268093(n): the number of valid 1 X n arrays with entries 0..2. -/
def a (n : ℕ) : ℕ := (Finset.univ.filter fun x : Fin n → Fin 3 => valid (List.ofFn x) = true).card

/-- The generating function Sum_{n >= 1} a(n) x^n (offset 1). -/
noncomputable def gf : ℚ⟦X⟧ := PowerSeries.mk fun n => if n = 0 then 0 else (a n : ℚ)

/-- Barker's conjectures: the g.f. and the closed form for n >= 1. -/
theorem main :
    gf = X * (1 - X - X ^ 2) * ((1 - 2 * X) * (1 - 2 * X - 2 * X ^ 2))⁻¹ ∧
    ∀ n : ℕ, 1 ≤ n → (a n : ℝ) = (-3 * 2 ^ n + (3 - 2 * Real.sqrt 3) * (1 - Real.sqrt 3) ^ n +
      (1 + Real.sqrt 3) ^ n * (3 + 2 * Real.sqrt 3)) / 12 := by
  sorry

end OMA.S_oeis_a268093

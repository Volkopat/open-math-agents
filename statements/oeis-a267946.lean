import Mathlib

/-!
# OEIS A267946: Barker's generating function and closed form

Source: https://oeis.org/A267946 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry (R. H. Hardin, Jan 22 2016), offset 1: Number of n X 1 0..2 arrays with every repeated
value in every row and column one larger mod 3 than the previous repeated value, and upper left
element zero. Data: 1, 3, 8, 21, 53, 132, 323, 783, ... Formula section: Conjectures from Colin
Barker, Mar 21 2018: G.f.: x*(1 - 2*x^2) / ((1 - 2*x)*(1 - x - 3*x^2)).
a(n) = 2^(-n)*(-39*4^n + (26-7*sqrt(13))*(1-sqrt(13))^n + (1+sqrt(13))^n*(26+7*sqrt(13))) / 39.

Formalization notes:
* An n X 1 array has rows of one element, so only its single column, read from the top, is
  constrained. A repeated value is an element equal to the element above it; each repeated value
  after the first must be one larger mod 3 than the previous repeated value of the column. The
  array is a function `Fin n → Fin 3` and its column is `List.ofFn x`.
* `ok r p l` scans the rest `l` of the column, where `p` is the element above it and `r` is the
  value of the last repeat so far (`none` before the first); `valid` adds that the upper left
  element is 0. This reading reproduces the first eleven terms of the entry's data by brute force.
* The g.f. is the formal power series Sum_{n >= 1} a(n) x^n over the rationals (offset 1, so the
  constant coefficient is 0), and the claim is that it equals the numerator times the inverse of
  the denominator, whose constant term is 1. The closed form is stated in the reals for n >= 1,
  with 2^(-n) as an integer power of 2 and sqrt as `Real.sqrt`.
* `main` is the conjunction of Barker's two conjectures.
* Controls (proved in the proof file): a(1..15) = 1, 3, 8, 21, 53, 132, 323, 783, 1880, 4485,
  10637, 25116, 59075, 138519, 323936, the entry's data, and a(4) = 21 by direct enumeration of
  the 81 arrays.
-/

namespace OMA.S_oeis_a267946

open PowerSeries

/-- Scanning a column from the top: `r` is the value at the last repeat so far (`none` before the
first repeat) and `p` is the element above the rest of the column. An element equal to the one
above it is a repeat, and its value must be one larger mod 3 than the value at the previous
repeat. -/
def ok : Option (Fin 3) → Fin 3 → List (Fin 3) → Bool
  | _, _, [] => true
  | r, p, c :: l =>
    if c = p then (r.all fun v => decide (c = v + 1)) && ok (some c) c l else ok r c l

/-- An n X 1 array, read as its single column from the top: the upper left element is 0 and the
column passes the scan. -/
def valid : List (Fin 3) → Bool
  | [] => true
  | c :: l => decide (c = 0) && ok none c l

/-- A267946(n): the number of valid n X 1 arrays with entries 0..2. -/
def a (n : ℕ) : ℕ := (Finset.univ.filter fun x : Fin n → Fin 3 => valid (List.ofFn x) = true).card

/-- The generating function Sum_{n >= 1} a(n) x^n (offset 1). -/
noncomputable def gf : ℚ⟦X⟧ := PowerSeries.mk fun n => if n = 0 then 0 else (a n : ℚ)

/-- Barker's conjectures: the g.f. and the closed form for n >= 1. -/
theorem main :
    gf = X * (1 - 2 * X ^ 2) * ((1 - 2 * X) * (1 - X - 3 * X ^ 2))⁻¹ ∧
    ∀ n : ℕ, 1 ≤ n → (a n : ℝ) = 2 ^ (-(n : ℤ)) * (-39 * 4 ^ n +
      (26 - 7 * Real.sqrt 13) * (1 - Real.sqrt 13) ^ n +
      (1 + Real.sqrt 13) ^ n * (26 + 7 * Real.sqrt 13)) / 39 := by
  sorry

end OMA.S_oeis_a267946

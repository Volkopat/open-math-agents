import Mathlib

/-!
# OEIS A268164: Barker's generating function and closed form

Source: https://oeis.org/A268164 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry (R. H. Hardin, Jan 27 2016), offset 1: number of n X 1 0..3 arrays with every repeated
value in every row and column one larger mod 4 than the previous repeated value, and upper left
element zero. Formula section: Conjectures from Colin Barker, Jan 11 2019:
G.f.: x*(1 - x - 3*x^2) / ((1 - 3*x)*(1 - 2*x - 4*x^2)).
a(n) = -3^n + (5/8-11/(8*sqrt(5)))*(1-sqrt(5))^n + (1/40)*(1+sqrt(5))^n*(25+11*sqrt(5)).

Formalization notes:
* An n X 1 array has rows of one element, so only its single column, read from the top, is
  constrained. A repeated value is an element equal to the element above it; each repeated value
  after the first must be one larger mod 4 than the previous repeated value of the column. The
  array is a function `Fin n → Fin 4` and its column is `List.ofFn x`.
* `ok r p l` scans the rest `l` of the column, where `p` is the element above it and `r` is the
  value of the last repeat so far (`none` before the first); `valid` adds that the upper left
  element is 0. This reading reproduces all thirteen terms of the entry's data, and the example
  columns of the entry pass the scan.
* The g.f. is the formal power series Sum_{n >= 1} a(n) x^n over the rationals (offset 1, so the
  constant coefficient is 0), and the claim is that it equals the numerator times the inverse of
  the denominator, whose constant term is 1. The closed form is stated in the reals for n >= 1,
  with -3^n read as -(3^n) and sqrt as `Real.sqrt`.
* `main` is the conjunction of Barker's two conjectures.
* Controls (proved in the proof file): a(1..5) = 1, 4, 15, 55, 197, the entry's data, and
  a(3) = 15 by direct enumeration of the 64 arrays.
-/

namespace OMA.S_oeis_a268164

open PowerSeries

/-- Scanning a column from the top: `r` is the value at the last repeat so far (`none` before the
first repeat) and `p` is the element above the rest of the column. An element equal to the one
above it is a repeat, and its value must be one larger mod 4 than the value at the previous
repeat. -/
def ok : Option (Fin 4) → Fin 4 → List (Fin 4) → Bool
  | _, _, [] => true
  | r, p, c :: l =>
    if c = p then (r.all fun v => decide (c = v + 1)) && ok (some c) c l else ok r c l

/-- An n X 1 array, read as its single column from the top: the upper left element is 0 and the
column passes the scan. -/
def valid : List (Fin 4) → Bool
  | [] => true
  | c :: l => decide (c = 0) && ok none c l

/-- A268164(n): the number of valid n X 1 arrays with entries 0..3. -/
def a (n : ℕ) : ℕ := (Finset.univ.filter fun x : Fin n → Fin 4 => valid (List.ofFn x) = true).card

/-- The generating function Sum_{n >= 1} a(n) x^n (offset 1). -/
noncomputable def gf : ℚ⟦X⟧ := PowerSeries.mk fun n => if n = 0 then 0 else (a n : ℚ)

/-- Barker's conjectures: the g.f. and the closed form for n >= 1. -/
theorem main :
    gf = X * (1 - X - 3 * X ^ 2) * ((1 - 3 * X) * (1 - 2 * X - 4 * X ^ 2))⁻¹ ∧
    ∀ n : ℕ, 1 ≤ n → (a n : ℝ) = -3 ^ n + (5 / 8 - 11 / (8 * Real.sqrt 5)) * (1 - Real.sqrt 5) ^ n +
      1 / 40 * (1 + Real.sqrt 5) ^ n * (25 + 11 * Real.sqrt 5) := by
  sorry

end OMA.S_oeis_a268164

import Mathlib

/-!
# OEIS A267905: Barker's generating function and closed form

Source: https://oeis.org/A267905 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry (R. H. Hardin, Jan 22 2016), offset 1: Number of n X 1 0..2 arrays with every repeated
value in every row unequal to the previous repeated value, and in every column equal to the
previous repeated value, and new values introduced in row-major sequential order. Data: 1, 2, 5,
13, 34, 88, 225, 569, ... Formula section: Conjectures from Colin Barker, Jan 11 2019:
G.f.: x*(1 - 3*x + 2*x^2 + x^3) / ((1 - x)*(1 - 2*x)*(1 - 2*x - x^2)).
a(n) = ((1-sqrt(2))^(1+n) + (1+sqrt(2))^(1+n) - 2*(2^n-1)) / 4.

Formalization notes:
* An n X 1 array has rows of one element, so the row condition is empty and only its single
  column, read from the top, is constrained. The array is a function `Fin n → Fin 3` and its
  column is `List.ofFn x`.
* A repeated value is an element equal to the element above it; each repeated value after the
  first must equal the previous repeated value of the column. New values introduced in row-major
  sequential order means that the values first appear in the order 0, 1, 2: the upper left
  element is 0, and each element is at most the number k of distinct values above it.
* `ok r p k l` scans the rest `l` of the column, where `p` is the element above it, `r` is the
  value at the last repeat so far (`none` before the first) and `k` is the number of distinct
  values seen so far; `valid` adds that the upper left element is 0. This reading reproduces the
  first twelve terms of the entry's data by brute force, and the example columns of the entry
  pass the scan.
* The g.f. is the formal power series Sum_{n >= 1} a(n) x^n over the rationals (offset 1, so the
  constant coefficient is 0), and the claim is that it equals the numerator times the inverse of
  the denominator, whose constant term is 1. The closed form is stated in the reals for n >= 1,
  with sqrt as `Real.sqrt`.
* `main` is the conjunction of Barker's two conjectures.
* Controls (proved in the proof file): a(1..13) = 1, 2, 5, 13, 34, 88, 225, 569, 1426, 3548,
  8777, 21613, 53026, the entry's data, and a(4) = 13 by direct enumeration of the 81 arrays.
-/

namespace OMA.S_oeis_a267905

open PowerSeries

/-- Scanning a column from the top. `r` is the value at the last repeat so far (`none` before the
first repeat), `p` is the element above the rest of the column and `k` is the number of distinct
values seen so far (they are 0, ..., k - 1). An element equal to the one above it is a repeat and
its value must equal the value at the previous repeat. Every element is at most k, so an element
that has not been seen is the next new value. -/
def ok : Option (Fin 3) → Fin 3 → ℕ → List (Fin 3) → Bool
  | _, _, _, [] => true
  | r, p, k, c :: l =>
    decide (c.val ≤ k) &&
      (if c = p then (r.all fun v => decide (c = v)) && ok (some c) c k l
        else ok r c (max k (c.val + 1)) l)

/-- An n X 1 array, read as its single column from the top: the upper left element is 0, the
first new value, and the rest of the column passes the scan. -/
def valid : List (Fin 3) → Bool
  | [] => true
  | c :: l => decide (c = 0) && ok none c 1 l

/-- A267905(n): the number of valid n X 1 arrays with entries 0..2. -/
def a (n : ℕ) : ℕ := (Finset.univ.filter fun x : Fin n → Fin 3 => valid (List.ofFn x) = true).card

/-- The generating function Sum_{n >= 1} a(n) x^n (offset 1). -/
noncomputable def gf : ℚ⟦X⟧ := PowerSeries.mk fun n => if n = 0 then 0 else (a n : ℚ)

/-- Barker's conjectures: the g.f. and the closed form for n >= 1. -/
theorem main :
    gf = X * (1 - 3 * X + 2 * X ^ 2 + X ^ 3) * ((1 - X) * (1 - 2 * X) * (1 - 2 * X - X ^ 2))⁻¹ ∧
    ∀ n : ℕ, 1 ≤ n → (a n : ℝ) =
      ((1 - Real.sqrt 2) ^ (1 + n) + (1 + Real.sqrt 2) ^ (1 + n) - 2 * (2 ^ n - 1)) / 4 := by
  sorry

end OMA.S_oeis_a267905

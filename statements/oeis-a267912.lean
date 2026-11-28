import Mathlib

/-!
# OEIS A267912: Barker's generating function and closed form

Source: https://oeis.org/A267912 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry (R. H. Hardin, Jan 22 2016), offset 1: Number of 1 X n 0..2 arrays with every repeated
value in every row unequal to the previous repeated value, and in every column equal to the
previous repeated value, and new values introduced in row-major sequential order. Data: 1, 2, 4,
11, 29, 77, 201, ... Formula section: Conjectures from Colin Barker, Feb 25 2018:
G.f.: x*(1 - x - 4*x^2 + 3*x^3 + 4*x^4) / ((1 - 2*x)*(1 - x - 4*x^2)).
a(n) = (1/17)*2^(-5-n)*(-17*4^(1+n) + (85-19*sqrt(17))*(1-sqrt(17))^n +
(1+sqrt(17))^n*(85+19*sqrt(17))) for n>2.

Formalization notes:
* A 1 X n array has columns of one element, so the column condition is empty and only its single
  row, read from the left, is constrained. A repeated value is an element equal to the element to
  its left; each repeated value after the first must differ from the previous repeated value of
  the row. New values introduced in row-major sequential order means that the values first appear
  in the order 0, 1, 2: the upper left element is 0, and each element is at most the number k of
  distinct values to its left. The array is a function `Fin n → Fin 3` and its row is
  `List.ofFn x`.
* `ok r p k l` scans the rest `l` of the row, where `p` is the element to its left, `r` is the
  value at the last repeat so far (`none` before the first) and `k` is the number of distinct
  values seen so far; `valid` adds that the upper left element is 0. This reading reproduces the
  first ten terms of the entry's data by brute force.
* The g.f. is the formal power series Sum_{n >= 1} a(n) x^n over the rationals (offset 1, so the
  constant coefficient is 0), and the claim is that it equals the numerator times the inverse of
  the denominator, whose constant term is 1. The closed form is stated in the reals for n > 2,
  with 2^(-5-n) as an integer power of 2 and sqrt as `Real.sqrt`.
* `main` is the conjunction of Barker's two conjectures.
* Controls (proved in the proof file): a(1..15) = 1, 2, 4, 11, 29, 77, 201, 525, 1361, 3525,
  9097, 23453, 60353, 155189, 398649, the entry's data, and a(4) = 11 by direct enumeration of the
  81 arrays.
-/

namespace OMA.S_oeis_a267912

open PowerSeries

/-- Scanning a row from the left. `r` is the value at the last repeat so far (`none` before the
first repeat), `p` is the element to the left of the rest of the row and `k` is the number of
distinct values seen so far (they are 0, ..., k - 1). An element equal to the one to its left is
a repeat and its value must differ from the value at the previous repeat. Every element is at
most k, so an element that has not been seen is the next new value. -/
def ok : Option (Fin 3) → Fin 3 → ℕ → List (Fin 3) → Bool
  | _, _, _, [] => true
  | r, p, k, c :: l =>
    decide (c.val ≤ k) &&
      (if c = p then (r.all fun v => decide (c ≠ v)) && ok (some c) c k l
        else ok r c (max k (c.val + 1)) l)

/-- A 1 X n array, read as its single row from the left: the upper left element is 0, the first
new value, and the rest of the row passes the scan. -/
def valid : List (Fin 3) → Bool
  | [] => true
  | c :: l => decide (c = 0) && ok none c 1 l

/-- A267912(n): the number of valid 1 X n arrays with entries 0..2. -/
def a (n : ℕ) : ℕ := (Finset.univ.filter fun x : Fin n → Fin 3 => valid (List.ofFn x) = true).card

/-- The generating function Sum_{n >= 1} a(n) x^n (offset 1). -/
noncomputable def gf : ℚ⟦X⟧ := PowerSeries.mk fun n => if n = 0 then 0 else (a n : ℚ)

/-- Barker's conjectures: the g.f. and the closed form for n > 2. -/
theorem main :
    gf = X * (1 - X - 4 * X ^ 2 + 3 * X ^ 3 + 4 * X ^ 4) *
      ((1 - 2 * X) * (1 - X - 4 * X ^ 2))⁻¹ ∧
    ∀ n : ℕ, 2 < n → (a n : ℝ) = 1 / 17 * 2 ^ (-5 - (n : ℤ)) * (-17 * 4 ^ (1 + n) +
      (85 - 19 * Real.sqrt 17) * (1 - Real.sqrt 17) ^ n +
      (1 + Real.sqrt 17) ^ n * (85 + 19 * Real.sqrt 17)) := by
  sorry

end OMA.S_oeis_a267912

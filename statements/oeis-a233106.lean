import Mathlib

/-!
# OEIS A233106: Barker's generating function and closed form

Source: https://oeis.org/A233106 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry (R. H. Hardin, Dec 04 2013), offset 1: Number of n X 1 0..5 arrays with no element x(i,j)
adjacent to value 5-x(i,j) horizontally or vertically, top left element zero, and 1 appearing
before 2 3 and 4, and 2 appearing before 3 in row major order. Data: 1, 2, 6, 23, 99, 452, 2136,
... Formula section: Conjectures from Colin Barker, Feb 19 2018:
G.f.: x*(1 - 7*x + 11*x^2) / ((1 - x)*(1 - 3*x)*(1 - 5*x)).
a(n) = (75 + 10*3^n + 3*5^n) / 120.

Formalization notes:
* An n X 1 array has only vertical neighbours, so the adjacency condition says that no two
  vertically adjacent elements sum to 5. Row major order is the order from the top. 1 appearing
  before 2, 3 and 4 means that no 2, 3 or 4 occurs before the first 1, and 2 appearing before 3
  means that no 3 occurs before the first 2 (the value 5 is not constrained). The array is a
  function `Fin n → Fin 6` and its column is `List.ofFn x`.
* `ok p s1 s2 l` scans the rest `l` of the column, where `p` is the element above it and `s1`,
  `s2` record whether a 1, a 2 has appeared; `valid` adds that the top left element is 0. This
  reading reproduces the first eight terms of the entry's data by brute force.
* The g.f. is the formal power series Sum_{n >= 1} a(n) x^n over the rationals (offset 1, so the
  constant coefficient is 0), and the claim is that it equals the numerator times the inverse of
  the denominator, whose constant term is 1. The closed form is stated in the rationals for the
  terms of the sequence, n >= 1.
* `main` is the conjunction of Barker's two conjectures.
* Controls (proved in the proof file): a(1..13) = 1, 2, 6, 23, 99, 452, 2136, 10313, 50469,
  249062, 1235466, 6147803, 30650439, the entry's data, and a(3) = 6 by direct enumeration of the
  216 arrays.
-/

namespace OMA.S_oeis_a233106

open PowerSeries

/-- Scanning a column from the top. `p` is the element above the rest of the column, `s1` says
whether a 1 has appeared and `s2` whether a 2 has appeared. No element is adjacent to 5 minus
itself, a 2, 3 or 4 may appear only after a 1 has appeared, and a 3 only after a 2 has appeared. -/
def ok : Fin 6 → Bool → Bool → List (Fin 6) → Bool
  | _, _, _, [] => true
  | p, s1, s2, c :: l =>
    decide (c.val + p.val ≠ 5) && (s1 || !decide (c.val = 2 ∨ c.val = 3 ∨ c.val = 4)) &&
      (s2 || decide (c.val ≠ 3)) && ok c (s1 || decide (c.val = 1)) (s2 || decide (c.val = 2)) l

/-- An n X 1 array, read as its single column from the top: the top left element is 0 and the
rest of the column passes the scan. -/
def valid : List (Fin 6) → Bool
  | [] => true
  | c :: l => decide (c = 0) && ok c false false l

/-- A233106(n): the number of valid n X 1 arrays with entries 0..5. -/
def a (n : ℕ) : ℕ := (Finset.univ.filter fun x : Fin n → Fin 6 => valid (List.ofFn x) = true).card

/-- The generating function Sum_{n >= 1} a(n) x^n (offset 1). -/
noncomputable def gf : ℚ⟦X⟧ := PowerSeries.mk fun n => if n = 0 then 0 else (a n : ℚ)

/-- Barker's conjectures: the g.f. and the closed form for n >= 1. -/
theorem main :
    gf = X * (1 - 7 * X + 11 * X ^ 2) * ((1 - X) * (1 - 3 * X) * (1 - 5 * X))⁻¹ ∧
    ∀ n : ℕ, 1 ≤ n → (a n : ℚ) = (75 + 10 * 3 ^ n + 3 * 5 ^ n) / 120 := by
  sorry

end OMA.S_oeis_a233106

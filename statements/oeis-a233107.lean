import Mathlib

/-!
# OEIS A233107: Barker's closed form and generating function

Source: https://oeis.org/A233107 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry (R. H. Hardin, Dec 04 2013), offset 1: Number of n X 2 0..5 arrays with no element x(i,j)
adjacent to value 5-x(i,j) horizontally or vertically, top left element zero, and 1 appearing
before 2 3 and 4, and 2 appearing before 3 in row major order. Data: 2, 19, 313, 6046, 123352,
2565169, ... The formula section states: Empirical: a(n) = 29*a(n-1) - 175*a(n-2) +
147*a(n-3). Conjectures from Colin Barker, Mar 19 2018: (Start) G.f.: x*(2 - 7*x)*(1 - 16*x) /
((1 - x)*(1 - 7*x)*(1 - 21*x)). a(n) = (105 + 18*7^n + 5*21^n) / 168. (End)

Formalization notes:
* An n X 2 array is a function `Fin n → Fin 6 × Fin 6` giving each row (x(i,0), x(i,1)); row
  major order reads the rows from the top, each from left to right. This follows the column
  version A233106, whose statement uses the same scan.
* Adjacent means horizontally or vertically adjacent, so no row has x(i,0) + x(i,1) = 5 and no
  two vertically adjacent elements sum to 5. 1 appearing before 2, 3 and 4 means that no 2, 3
  or 4 occurs before the first 1, and 2 appearing before 3 means that no 3 occurs before the
  first 2; the values 0 and 5 are not constrained. `ok` scans the rows below a given row with
  the flags s1, s2 (a 1, a 2 has appeared), and `valid` adds the first row and the top left 0.
  This reading reproduces the entry's data a(1..13).
* The closed form is stated in the rationals for the terms of the sequence, n >= 1. The g.f.
  is A(x) = Sum_{n >= 1} a(n) x^n (offset 1), stated as A(x) (1 - x)(1 - 7x)(1 - 21x) =
  x(2 - 7x)(1 - 16x) in Z[[x]], which is equivalent because the denominator has constant
  term 1.
* `main` is the conjunction of Barker's two conjectures.
* Controls proved in the proof file: a(1..13), all the entry's listed terms.
-/

namespace OMA.S_oeis_a233107

open PowerSeries

/-- A cell may hold 2, 3 or 4 only once a 1 has appeared (`s1`), and 3 only once a 2 has
appeared (`s2`). -/
def cellOk (c : Fin 6) (s1 s2 : Bool) : Bool :=
  (s1 || !decide (c.val = 2 ∨ c.val = 3 ∨ c.val = 4)) && (s2 || decide (c.val ≠ 3))

/-- Scanning the rows below the row (pu, pv) in row major order, where `s1`, `s2` record whether
a 1, a 2 has appeared: no element is adjacent, horizontally or vertically, to 5 minus itself, and
every cell passes `cellOk` with the flags of the cells before it. -/
def ok : Fin 6 → Fin 6 → Bool → Bool → List (Fin 6 × Fin 6) → Bool
  | _, _, _, _, [] => true
  | pu, pv, s1, s2, c :: l =>
    decide (c.1.val + pu.val ≠ 5) && decide (c.2.val + pv.val ≠ 5) &&
      decide (c.1.val + c.2.val ≠ 5) && cellOk c.1 s1 s2 &&
      cellOk c.2 (s1 || decide (c.1.val = 1)) (s2 || decide (c.1.val = 2)) &&
      ok c.1 c.2 (s1 || decide (c.1.val = 1) || decide (c.2.val = 1))
        (s2 || decide (c.1.val = 2) || decide (c.2.val = 2)) l

/-- An n X 2 array, read as its list of rows from the top: the top left element is 0, the first
row passes the conditions with no 1 or 2 before it, and the rows below pass the scan. -/
def valid : List (Fin 6 × Fin 6) → Bool
  | [] => true
  | c :: l =>
    decide (c.1 = 0) && decide (c.1.val + c.2.val ≠ 5) && cellOk c.1 false false &&
      cellOk c.2 (decide (c.1.val = 1)) (decide (c.1.val = 2)) &&
      ok c.1 c.2 (decide (c.1.val = 1) || decide (c.2.val = 1))
        (decide (c.1.val = 2) || decide (c.2.val = 2)) l

/-- A233107(n): the number of valid n X 2 arrays with entries 0..5; row i is the pair
(x(i,0), x(i,1)). -/
def a (n : ℕ) : ℕ := (Finset.univ.filter fun x : Fin n → Fin 6 × Fin 6 => valid (List.ofFn x) = true).card

/-- Barker's conjectures: the closed form and the g.f. -/
theorem main :
    (∀ n : ℕ, 1 ≤ n → (a n : ℚ) = (105 + 18 * 7 ^ n + 5 * 21 ^ n) / 168) ∧
    PowerSeries.mk (fun n => if n = 0 then (0 : ℤ) else a n) * ((1 - X) * (1 - 7 * X) * (1 - 21 * X)) =
      X * (2 - 7 * X) * (1 - 16 * X) := by
  sorry

end OMA.S_oeis_a233107

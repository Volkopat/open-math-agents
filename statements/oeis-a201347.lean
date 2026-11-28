import Mathlib

/-!
# OEIS A201347: Barker's generating function and recurrence

Source: https://oeis.org/A201347 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry (R. H. Hardin, Nov 30 2011), offset 1: Number of n X 2 0..1 arrays with rows and columns
lexicographically nondecreasing and every element equal to at least one horizontal or vertical
neighbor. Data: 2, 4, 8, 14, 23, 36, 54, 78, ... Formula section: Conjectures from Colin
Barker, May 22 2018: G.f.: x*(2 - 4*x + 4*x^2 - 2*x^3 + x^4) / (1 - x)^4.
a(n) = 4*a(n-1) - 6*a(n-2) + 4*a(n-3) - a(n-4) for n>5.

Formalization notes:
* The rows (x(i,0), x(i,1)) are lexicographically nondecreasing from the top, and the two
  columns, read from the top, are lexicographically nondecreasing from left to right: at the
  first row with x(i,0) ≠ x(i,1) (if any), x(i,0) < x(i,1). Every element equals its horizontal
  partner or the element above or below it. The lexicographic order on rows is written out
  (Mathlib's order on pairs is the product order).
* `ok r t s0 s1 l` scans the rows `l` below the row `r`: `t` records whether the columns are
  already strictly ordered, `s0` and `s1` whether the elements of `r` already have an equal
  neighbour; `valid` starts the scan at the first row. This reading reproduces the first eight
  terms of the entry's data by brute force.
* The g.f. is the formal power series Sum_{n >= 1} a(n) x^n over the rationals (offset 1, so the
  constant coefficient is 0), and the claim is that it equals the numerator times the inverse of
  the denominator, whose constant term is 1. The recurrence is stated in the integers for n > 5.
* `main` is the conjunction of Barker's two conjectures.
* Controls (proved in the proof file): a(1..19) = 2, 4, 8, 14, 23, 36, 54, 78, 109, 148, 196, 254,
  323, 404, 498, 606, 729, 868, 1024, the entry's data, and a(4) = 14 by direct enumeration of the
  256 arrays with four rows.
-/

namespace OMA.S_oeis_a201347

open PowerSeries

/-- Scanning the rows from the top. `r` is the row above the rest of the array; `t` says whether
some row so far has x(i,0) < x(i,1), so that column 0 is already lexicographically smaller than
column 1; `s0` and `s1` say whether the two elements of `r` already equal one of their neighbours
(the other element of `r` or the element above). Each new row is lexicographically at least `r`;
while `t` is false it must have x(i,0) <= x(i,1); an element of `r` that differs from the element
below it must already have an equal neighbour; at the end both elements of the last row must
have one. -/
def ok : Fin 2 × Fin 2 → Bool → Bool → Bool → List (Fin 2 × Fin 2) → Bool
  | _, _, s0, s1, [] => s0 && s1
  | r, t, s0, s1, w :: l =>
    decide (r.1 < w.1 ∨ (r.1 = w.1 ∧ r.2 ≤ w.2)) && (t || decide (w.1 ≤ w.2)) &&
      (s0 || decide (w.1 = r.1)) && (s1 || decide (w.2 = r.2)) &&
      ok w (t || decide (w.1 < w.2)) (decide (w.1 = w.2) || decide (w.1 = r.1))
        (decide (w.2 = w.1) || decide (w.2 = r.2)) l

/-- An n X 2 array, given by its rows (x(i,0), x(i,1)) from the top: the first row has
x(0,0) <= x(0,1) (columns lexicographically ordered), its elements have an equal neighbour so far
exactly when they are equal, and the rest of the rows pass the scan. -/
def valid : List (Fin 2 × Fin 2) → Bool
  | [] => true
  | w :: l =>
    decide (w.1 ≤ w.2) && ok w (decide (w.1 < w.2)) (decide (w.1 = w.2)) (decide (w.1 = w.2)) l

/-- A201347(n): the number of valid n X 2 arrays with entries 0..1. -/
def a (n : ℕ) : ℕ :=
  (Finset.univ.filter fun x : Fin n → Fin 2 × Fin 2 => valid (List.ofFn x) = true).card

/-- The generating function Sum_{n >= 1} a(n) x^n (offset 1). -/
noncomputable def gf : ℚ⟦X⟧ := PowerSeries.mk fun n => if n = 0 then 0 else (a n : ℚ)

/-- Barker's conjectures: the g.f. and the recurrence for n > 5. -/
theorem main :
    gf = X * (2 - 4 * X + 4 * X ^ 2 - 2 * X ^ 3 + X ^ 4) * ((1 - X) ^ 4)⁻¹ ∧
    ∀ n : ℕ, 5 < n → (a n : ℤ) = 4 * a (n - 1) - 6 * a (n - 2) + 4 * a (n - 3) - a (n - 4) := by
  sorry

end OMA.S_oeis_a201347

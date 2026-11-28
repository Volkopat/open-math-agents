import Mathlib

/-!
# OEIS A222939: Barker's generating function and closed form

Source: https://oeis.org/A222939 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry (R. H. Hardin, Mar 09 2013), offset 1: Number of n X 1 0..4 arrays with no element equal
to another at a city block distance of exactly two, and new values 0..4 introduced in row major
order. Data: 1, 2, 3, 7, 20, 66, 238, 902, ... Formula section: Conjectures from Colin Barker,
Aug 16 2018: G.f.: x*(1 + x)*(1 - 6*x + 9*x^2 - 3*x^3) / ((1 - x)*(1 - 2*x)*(1 - 4*x)).
a(n) = (256 + 9*2^(3+n) + 5*4^n) / 384 for n>2.

Formalization notes:
* In an n X 1 array the elements at city block distance exactly two from an element are the ones
  two rows above and two rows below it, so the condition says that no element equals the element
  two rows above it. New values introduced in row major order means that the values first appear
  in the order 0, 1, 2, 3, 4 from the top: the top element is 0, and each element is at most the
  number k of distinct values above it. The array is a function `Fin n → Fin 5` and its column is
  `List.ofFn x`.
* `ok q p k l` scans the rest `l` of the column, where `q` is the element two rows above it
  (`none` at the start), `p` the element directly above it and `k` the number of values used so
  far; `valid` adds that the top element is 0. This reading reproduces the first nine terms of the
  entry's data by brute force.
* The g.f. is the formal power series Sum_{n >= 1} a(n) x^n over the rationals (offset 1, so the
  constant coefficient is 0), and the claim is that it equals the numerator times the inverse of
  the denominator, whose constant term is 1. The closed form is stated in the rationals for
  n > 2.
* `main` is the conjunction of Barker's two conjectures.
* Controls (proved in the proof file): a(1..14) = 1, 2, 3, 7, 20, 66, 238, 902, 3510, 13846,
  54998, 219222, 875350, 3498326, the entry's data, and a(4) = 7 by direct enumeration of the 625
  arrays.
-/

namespace OMA.S_oeis_a222939

open PowerSeries

/-- Scanning a column from the top. `q` is the element two rows above the rest of the column
(`none` at the start), `p` the element directly above it, and `k` the number of values used so
far (they are 0, ..., k - 1). An element may not equal the element two rows above it (the only
other element at city block distance two in a column), and every element is at most k, so a value
that has not been used is the next new value. -/
def ok : Option (Fin 5) → Fin 5 → ℕ → List (Fin 5) → Bool
  | _, _, _, [] => true
  | q, p, k, c :: l =>
    decide (c.val ≤ k) && (q.all fun v => decide (c ≠ v)) && ok (some p) c (max k (c.val + 1)) l

/-- An n X 1 array, read as its single column from the top: the top element is 0, the first new
value, and the rest of the column passes the scan. -/
def valid : List (Fin 5) → Bool
  | [] => true
  | c :: l => decide (c = 0) && ok none c 1 l

/-- A222939(n): the number of valid n X 1 arrays with entries 0..4. -/
def a (n : ℕ) : ℕ := (Finset.univ.filter fun x : Fin n → Fin 5 => valid (List.ofFn x) = true).card

/-- The generating function Sum_{n >= 1} a(n) x^n (offset 1). -/
noncomputable def gf : ℚ⟦X⟧ := PowerSeries.mk fun n => if n = 0 then 0 else (a n : ℚ)

/-- Barker's conjectures: the g.f. and the closed form for n > 2. -/
theorem main :
    gf = X * (1 + X) * (1 - 6 * X + 9 * X ^ 2 - 3 * X ^ 3) *
      ((1 - X) * (1 - 2 * X) * (1 - 4 * X))⁻¹ ∧
    ∀ n : ℕ, 2 < n → (a n : ℚ) = (256 + 9 * 2 ^ (3 + n) + 5 * 4 ^ n) / 384 := by
  sorry

end OMA.S_oeis_a222939

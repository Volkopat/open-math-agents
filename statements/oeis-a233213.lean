import Mathlib

/-!
# OEIS A233213: Barker's generating function and closed form

Source: https://oeis.org/A233213 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @marcusbuffett.
No human mathematician has reviewed this translation; please review it as strictly as any other.

Entry (R. H. Hardin, Dec 06 2013), offset 1: Number of n X 4 0..5 arrays with no element x(i,j)
adjacent to value 5-x(i,j) horizontally or antidiagonally, top left element zero, and 1 appearing
before 2 3 and 4, and 2 appearing before 3 in row major order. Data: 23, 7222, 3054973,
1340889772, 591021089923, ... Formula section: Empirical: a(n) = 491*a(n-1) - 22099*a(n-2) +
21609*a(n-3). Conjectures from Colin Barker, Oct 10 2018:
G.f.: x*(23 - 4071*x + 17248*x^2) / ((1 - x)*(1 - 49*x)*(1 - 441*x)).
a(n) = (2205 + 486*49^n + 125*441^n) / 3528.

Formalization notes:
* An n X 4 array with entries 0..5 is a map `x : Fin n → Fin 4 → Fin 6`, with x(i,j) = `x i j`;
  row i is the map `x i`, and the array is read as its list of rows from the top,
  `List.ofFn x`. Values are compared as natural numbers.
* Horizontally adjacent elements are x(i,j) and x(i,j+1); antidiagonally adjacent elements are
  x(i,j+1) and x(i+1,j), i.e. x(i,j) and x(i+1,j-1). Since x(i,j) = 5 - y exactly when y =
  5 - x(i,j), the adjacency condition says that no two adjacent elements sum to 5 (`horizOk`
  inside a row, `antiOk` between a row `p` and the row `r` directly below it). An element may be
  adjacent to an equal element.
* 1 appearing before 2, 3 and 4 means that no 2, 3 or 4 occurs before the first 1 in row major
  order (left to right in each row, rows from the top), and 2 appearing before 3 means that no 3
  occurs before the first 2; the value 5 is not constrained, and values that do not occur
  impose nothing. `cellOk c s1 s2` is this condition for a cell holding c, where `s1`, `s2` say
  whether a 1, a 2 occurs among the cells before it in row major order; `rowOk r s1 s2` checks
  the four cells of a row from the left, given the flags `s1`, `s2` of the rows above it, and
  `seen1`, `seen2` update the flags after a row.
* `ok p s1 s2 l` scans the rows `l` below the row `p`; `valid` adds that the top left element
  is 0 and checks the first row with no 1 or 2 before it.
* This reading reproduces every listed term of the entry (n = 1..11) by a transfer-matrix
  computation, and a(1) = 23, a(2) = 7222 by direct enumeration of all 6^4 and 6^8 arrays
  against the entry's wording.
* The g.f. is the formal power series Sum_{n >= 1} a(n) x^n over the rationals (offset 1, so the
  constant coefficient is 0), and the claim is that it equals the numerator times the inverse of
  the denominator, whose constant term is 1. The closed form is stated in the rationals for the
  terms of the sequence, n >= 1. `main` is the conjunction of Barker's two conjectures.
-/

namespace OMA.S_oeis_a233213

open PowerSeries

/-- A cell holding c, where `s1`, `s2` say whether a 1, a 2 occurs before it in row major order:
a 2, 3 or 4 may occur only after a 1, and a 3 only after a 2. -/
def cellOk (c : Fin 6) (s1 s2 : Bool) : Bool :=
  (s1 || !decide (c.val = 2 ∨ c.val = 3 ∨ c.val = 4)) && (s2 || decide (c.val ≠ 3))

/-- No two horizontally adjacent elements of the row r sum to 5. -/
def horizOk (r : Fin 4 → Fin 6) : Bool :=
  decide (∀ j : Fin 3, (r j.castSucc).val + (r j.succ).val ≠ 5)

/-- No element of the row p is antidiagonally adjacent, in the row r directly below p, to 5 minus
itself: x(i,j+1) + x(i+1,j) is never 5. -/
def antiOk (p r : Fin 4 → Fin 6) : Bool :=
  decide (∀ j : Fin 3, (p j.succ).val + (r j.castSucc).val ≠ 5)

/-- The row r passes `horizOk`, and its cells, read from the left, pass `cellOk`, where `s1`,
`s2` are the flags of the rows above it. -/
def rowOk (r : Fin 4 → Fin 6) (s1 s2 : Bool) : Bool :=
  horizOk r && cellOk (r 0) s1 s2 &&
    cellOk (r 1) (s1 || decide (r 0 = 1)) (s2 || decide (r 0 = 2)) &&
    cellOk (r 2) (s1 || decide (r 0 = 1) || decide (r 1 = 1))
      (s2 || decide (r 0 = 2) || decide (r 1 = 2)) &&
    cellOk (r 3) (s1 || decide (r 0 = 1) || decide (r 1 = 1) || decide (r 2 = 1))
      (s2 || decide (r 0 = 2) || decide (r 1 = 2) || decide (r 2 = 2))

/-- Whether a 1 occurs in the row r or before it. -/
def seen1 (r : Fin 4 → Fin 6) (s1 : Bool) : Bool := s1 || decide (∃ j, r j = 1)

/-- Whether a 2 occurs in the row r or before it. -/
def seen2 (r : Fin 4 → Fin 6) (s2 : Bool) : Bool := s2 || decide (∃ j, r j = 2)

/-- Scanning the rows `l` below the row p, where `s1`, `s2` say whether a 1, a 2 occurs in p or
above it. -/
def ok : (Fin 4 → Fin 6) → Bool → Bool → List (Fin 4 → Fin 6) → Bool
  | _, _, _, [] => true
  | p, s1, s2, r :: l => antiOk p r && rowOk r s1 s2 && ok r (seen1 r s1) (seen2 r s2) l

/-- An n X 4 array, read as its list of rows from the top: the top left element is 0, the first
row passes `rowOk` with nothing before it, and the rows below pass the scan. -/
def valid : List (Fin 4 → Fin 6) → Bool
  | [] => true
  | r :: l => decide (r 0 = 0) && rowOk r false false && ok r (seen1 r false) (seen2 r false) l

/-- A233213(n): the number of valid n X 4 arrays with entries 0..5. -/
def a (n : ℕ) : ℕ :=
  (Finset.univ.filter fun x : Fin n → Fin 4 → Fin 6 => valid (List.ofFn x) = true).card

/-- The generating function Sum_{n >= 1} a(n) x^n (offset 1). -/
noncomputable def gf : ℚ⟦X⟧ := PowerSeries.mk fun n => if n = 0 then 0 else (a n : ℚ)

/-- Barker's conjectures: the g.f. and the closed form for n >= 1. -/
theorem main :
    gf = X * (23 - 4071 * X + 17248 * X ^ 2) * ((1 - X) * (1 - 49 * X) * (1 - 441 * X))⁻¹ ∧
    ∀ n : ℕ, 1 ≤ n → (a n : ℚ) = (2205 + 486 * 49 ^ n + 125 * 441 ^ n) / 3528 := by
  sorry

end OMA.S_oeis_a233213

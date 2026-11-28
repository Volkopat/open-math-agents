import Mathlib

/-!
# OEIS A201722: Barker's generating function and recurrence

Source: https://oeis.org/A201722 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry (R. H. Hardin, Dec 04 2011), offset 1: Number of n X 1 0..4 arrays with rows and columns
lexicographically nondecreasing and no element equal to the number of horizontal and vertical
neighbors equal to itself. Data: 4, 10, 20, 35, 56, 83, 116, ... Formula section: Conjectures
from Colin Barker, May 23 2018: G.f.: x*(4 - 2*x + 2*x^2 + x^3 + x^4) / (1 - x)^3.
a(n) = 3*a(n-1) - 3*a(n-2) + a(n-3) for n>5.

Formalization notes:
* The rows of an n X 1 array are its single elements, so the rows are lexicographically
  nondecreasing exactly when the column, read from the top, is nondecreasing; the single column
  imposes nothing. There are no horizontal neighbours, so the number of neighbours equal to an
  element counts the element above and the element below it (0, 1 or 2), and it must differ from
  the element. The array is a function `Fin n → Fin 5` and its column is `List.ofFn x`.
* `ok p r l` scans the rest `l` of the column, where `p` is the element above it and `r` the
  number of neighbours of `p` equal to it so far (the element above `p`); `valid` starts the scan
  at the top element. This reading reproduces the first eight terms of the entry's data by brute
  force.
* The g.f. is the formal power series Sum_{n >= 1} a(n) x^n over the rationals (offset 1, so the
  constant coefficient is 0), and the claim is that it equals the numerator times the inverse of
  the denominator, whose constant term is 1. The recurrence is stated in the integers for n > 5.
* `main` is the conjunction of Barker's two conjectures.
* Controls (proved in the proof file): a(1..19) = 4, 10, 20, 35, 56, 83, 116, 155, 200, 251, 308,
  371, 440, 515, 596, 683, 776, 875, 980, the entry's data, and a(4) = 35 by direct enumeration of
  the 625 arrays.
-/

namespace OMA.S_oeis_a201722

open PowerSeries

/-- Scanning a column from the top. `p` is the element above the rest of the column and `r` the
number of its neighbours equal to it so far (the element above it). The rows, read from the top,
are nondecreasing, and no element equals the number of its vertical neighbours equal to itself:
the count of `p` is final once the next element is known, and that of the last element at the
end. -/
def ok : Fin 5 → ℕ → List (Fin 5) → Bool
  | p, r, [] => decide (r ≠ p.val)
  | p, r, c :: l =>
    decide (p ≤ c) &&
      (if c = p then decide (r + 1 ≠ p.val) && ok c 1 l else decide (r ≠ p.val) && ok c 0 l)

/-- An n X 1 array, read as its single column from the top, that passes the scan. -/
def valid : List (Fin 5) → Bool
  | [] => true
  | c :: l => ok c 0 l

/-- A201722(n): the number of valid n X 1 arrays with entries 0..4. -/
def a (n : ℕ) : ℕ := (Finset.univ.filter fun x : Fin n → Fin 5 => valid (List.ofFn x) = true).card

/-- The generating function Sum_{n >= 1} a(n) x^n (offset 1). -/
noncomputable def gf : ℚ⟦X⟧ := PowerSeries.mk fun n => if n = 0 then 0 else (a n : ℚ)

/-- Barker's conjectures: the g.f. and the recurrence for n > 5. -/
theorem main :
    gf = X * (4 - 2 * X + 2 * X ^ 2 + X ^ 3 + X ^ 4) * ((1 - X) ^ 3)⁻¹ ∧
    ∀ n : ℕ, 5 < n → (a n : ℤ) = 3 * a (n - 1) - 3 * a (n - 2) + a (n - 3) := by
  sorry

end OMA.S_oeis_a201722

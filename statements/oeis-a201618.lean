import Mathlib

/-!
# OEIS A201618: Barker's generating function and recurrence

Source: https://oeis.org/A201618 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry (R. H. Hardin, Dec 03 2011), offset 1: Number of n X 1 0..3 arrays with rows and columns
lexicographically nondecreasing and every element equal to at least one horizontal or vertical
neighbor. Data: 0, 4, 4, 10, 16, 26, 40, 59, 84, ... Formula section: Conjectures from Colin
Barker, May 23 2018:
G.f.: x^2*(2 - 2*x + x^2)*(2 - 4*x + 4*x^2 - 2*x^3 + x^4) / (1 - x)^4.
a(n) = 4*a(n-1) - 6*a(n-2) + 4*a(n-3) - a(n-4) for n>8.

Formalization notes:
* The rows of an n X 1 array are its single elements, so the rows are lexicographically
  nondecreasing exactly when the column, read from the top, is nondecreasing; the single column
  imposes nothing. There are no horizontal neighbours, so every element must equal the element
  above or the element below it. The array is a function `Fin n → Fin 4` and its column is
  `List.ofFn x`.
* `ok p s l` scans the rest `l` of the column, where `p` is the element above it and `s` records
  whether `p` already equals the element above it; `valid` starts the scan at the top element.
  This reading reproduces the first ten terms of the entry's data by brute force.
* The g.f. is the formal power series Sum_{n >= 1} a(n) x^n over the rationals (offset 1, so the
  constant coefficient is 0), and the claim is that it equals the numerator times the inverse of
  the denominator, whose constant term is 1. The recurrence is stated in the integers for n > 8.
* `main` is the conjunction of Barker's two conjectures.
* Controls (proved in the proof file): a(1..20) = 0, 4, 4, 10, 16, 26, 40, 59, 84, 116, 156, 205,
  264, 334, 416, 511, 620, 744, 884, 1041, the entry's data, and a(4) = 10 by direct enumeration
  of the 256 arrays.
-/

namespace OMA.S_oeis_a201618

open PowerSeries

/-- Scanning a column from the top. `p` is the element above the rest of the column and `s` says
whether `p` is already equal to one of its neighbours (the element above it). The rows, read from
the top, are nondecreasing, and every element equals at least one of its vertical neighbours:
when the next element differs from `p`, `p` must already have an equal neighbour, and at the end
the last element must have one. -/
def ok : Fin 4 → Bool → List (Fin 4) → Bool
  | _, s, [] => s
  | p, s, c :: l => decide (p ≤ c) && (if c = p then ok c true l else s && ok c false l)

/-- An n X 1 array, read as its single column from the top, that passes the scan. -/
def valid : List (Fin 4) → Bool
  | [] => true
  | c :: l => ok c false l

/-- A201618(n): the number of valid n X 1 arrays with entries 0..3. -/
def a (n : ℕ) : ℕ := (Finset.univ.filter fun x : Fin n → Fin 4 => valid (List.ofFn x) = true).card

/-- The generating function Sum_{n >= 1} a(n) x^n (offset 1). -/
noncomputable def gf : ℚ⟦X⟧ := PowerSeries.mk fun n => if n = 0 then 0 else (a n : ℚ)

/-- Barker's conjectures: the g.f. and the recurrence for n > 8. -/
theorem main :
    gf = X ^ 2 * (2 - 2 * X + X ^ 2) * (2 - 4 * X + 4 * X ^ 2 - 2 * X ^ 3 + X ^ 4) *
      ((1 - X) ^ 4)⁻¹ ∧
    ∀ n : ℕ, 8 < n → (a n : ℤ) = 4 * a (n - 1) - 6 * a (n - 2) + 4 * a (n - 3) - a (n - 4) := by
  sorry

end OMA.S_oeis_a201618

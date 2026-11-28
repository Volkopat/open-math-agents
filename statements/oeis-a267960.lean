import Mathlib

/-!
# OEIS A267960: Barker's generating function and closed forms

Source: https://oeis.org/A267960 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry (R. H. Hardin, Jan 22 2016), offset 1: Number of n X 1 0..2 arrays with every repeated
value in every row and column greater than the previous repeated value. Data: 3, 9, 24, 63, 159,
394, 957, ... Formula section: Conjectures from Colin Barker, Feb 25 2018:
G.f.: x*(3 - 9*x - 3*x^2 + 24*x^3 - 3*x^4 - 17*x^5) / ((1 + x)^2*(1 - 2*x)^4).
a(n) = (96*n + 2^n*(9*n*(n*(n+44)+445)+7622) + 640) / 7776 for n even.
a(n) = (2^n*(9*n*(n*(n+44)+445)+7622) - 32*(3*n+20)) / 7776 for n odd.

Formalization notes:
* An n X 1 array has rows of one element, so only its single column, read from the top, is
  constrained. A repeated value is an element equal to the element above it; each repeated value
  after the first must be greater than the previous repeated value of the column. The array is a
  function `Fin n → Fin 3` and its column is `List.ofFn x`.
* `ok r p l` scans the rest `l` of the column, where `p` is the element above it and `r` is the
  value of the last repeat so far (`none` before the first). This reading reproduces the first
  eleven terms of the entry's data by brute force.
* The g.f. is the formal power series Sum_{n >= 1} a(n) x^n over the rationals (offset 1, so the
  constant coefficient is 0), and the claim is that it equals the numerator times the inverse of
  the denominator, whose constant term is 1. The two closed forms are stated in the rationals for
  the terms of the sequence, n >= 1, even or odd.
* `main` is the conjunction of Barker's three conjectures.
* Controls (proved in the proof file): a(1..14) = 3, 9, 24, 63, 159, 394, 957, 2292, 5419, 12678,
  29385, 67560, 154215, 349770, the entry's data, and a(4) = 63 by direct enumeration of the 81
  arrays.
-/

namespace OMA.S_oeis_a267960

open PowerSeries

/-- Scanning a column from the top: `r` is the value at the last repeat so far (`none` before the
first repeat) and `p` is the element above the rest of the column. An element equal to the one
above it is a repeat, and its value must be greater than the value at the previous repeat. -/
def ok : Option (Fin 3) → Fin 3 → List (Fin 3) → Bool
  | _, _, [] => true
  | r, p, c :: l =>
    if c = p then (r.all fun v => decide (v < c)) && ok (some c) c l else ok r c l

/-- An n X 1 array, read as its single column from the top, whose repeats pass the scan. -/
def valid : List (Fin 3) → Bool
  | [] => true
  | c :: l => ok none c l

/-- A267960(n): the number of valid n X 1 arrays with entries 0..2. -/
def a (n : ℕ) : ℕ := (Finset.univ.filter fun x : Fin n → Fin 3 => valid (List.ofFn x) = true).card

/-- The generating function Sum_{n >= 1} a(n) x^n (offset 1). -/
noncomputable def gf : ℚ⟦X⟧ := PowerSeries.mk fun n => if n = 0 then 0 else (a n : ℚ)

/-- Barker's conjectures: the g.f. and the closed forms for even and odd n >= 1. -/
theorem main :
    gf = X * (3 - 9 * X - 3 * X ^ 2 + 24 * X ^ 3 - 3 * X ^ 4 - 17 * X ^ 5) *
      ((1 + X) ^ 2 * (1 - 2 * X) ^ 4)⁻¹ ∧
    (∀ n : ℕ, 1 ≤ n → Even n →
      (a n : ℚ) = (96 * n + 2 ^ n * (9 * n * (n * (n + 44) + 445) + 7622) + 640) / 7776) ∧
    (∀ n : ℕ, 1 ≤ n → Odd n →
      (a n : ℚ) = (2 ^ n * (9 * n * (n * (n + 44) + 445) + 7622) - 32 * (3 * n + 20)) / 7776) := by
  sorry

end OMA.S_oeis_a267960

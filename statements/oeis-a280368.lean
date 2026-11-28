import Mathlib

/-!
# OEIS A280368: Barker's closed forms, recurrence and g.f. for the x-axis of the 2D Rule 259

Source: https://oeis.org/A280368 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry A280368 (Robert Price, Jan 01 2017), offset 0: Binary representation of the x-axis, from the
origin to the right edge, of the n-th stage of growth of the two-dimensional cellular automaton
defined by Rule 259, based on the 5-celled von Neumann neighborhood.
Formula section:
Conjectures from Colin Barker, Jan 01 2017:
a(n) = (989*(-10)^n + 991*10^n)/1800 for n>1 and even.
a(n) = (989*(-10)^n + 991*10^n - 200)/1800 for n>1 and odd.
a(n) = 101*a(n-2) - 100*a(n-4) for n>5.
G.f.: (1 + 10*x + 9*x^2 - 1009*x^3 - 10*x^4 + 1010*x^5) / ((1 - x)*(1 + x)*(1 - 10*x)*(1 + 10*x)).

Formalization notes:
* Rule numbering: Wolfram's outer totalistic code on the 5-celled von Neumann neighborhood, as
  CAStep in the entry's program: the new state of a cell is bit 2k + c of the rule number, where c
  is its old state and k the number of its four neighbors (x +- 1, y) and (x, y +- 1) that are ON.
* Initial condition: at stage 0 the origin is ON and every other cell of Z x Z is OFF; each stage
  applies the rule to every cell of the plane, so the background evolves with the rule (Rule 259
  turns an OFF cell with no ON neighbor ON); the entry's program evolves the same rule on a finite
  grid.
* Reading convention: a(n) writes the cells (0, 0), ..., (n, 0) of stage n (origin first) as binary
  digits and reads them as a decimal number, as the entry's program does (the middle row of the
  trimmed stage, from the center to the right edge, FromDigits).
* The statement is the conjunction of the 4 conjectures of the site's problem, in the entry's order.
  The recurrence is stated in the integers. The closed forms are stated in the rationals, where
  every division is exact. The generating function is A(x) = Sum_{n >= 0} a(n) x^n in the formal
  power series ring over the rationals, and the identity is A = N * D⁻¹, where D has a nonzero
  constant term.
* Controls proved in the proof file (theorem vals): the definition gives a(n) for n = 0..19 equal to
  the entry's first 20 terms, 1, 10, 110, 1, 11000, 111, 1100000, 11111, 110000000, 1111111,
  11000000000, 111111111, ....
-/

namespace OMA.S_oeis_a280368

open PowerSeries

/-- Rule 259: new state from the cell's state `c` and its number `k` of ON neighbors
(Wolfram's outer totalistic code: bit `2k + c` of 259). -/
def rule (c : Bool) (k : ℕ) : Bool := (259 : ℕ).testBit (2 * k + cond c 1 0)

/-- The four von Neumann neighbors. -/
def nbrs (p : ℤ × ℤ) : List (ℤ × ℤ) :=
  [(p.1 + 1, p.2), (p.1 - 1, p.2), (p.1, p.2 + 1), (p.1, p.2 - 1)]

/-- The automaton on `ℤ × ℤ`, started from the single ON cell at the origin. -/
def state : ℕ → ℤ × ℤ → Bool
  | 0, p => decide (p = (0, 0))
  | t + 1, p => rule (state t p) ((nbrs p).countP (fun q => state t q))

/-- A280368(n): the cells `(0,0), ..., (n,0)` of stage `n` (origin first) as binary digits read in base 10. -/
def a (n : ℕ) : ℕ :=
  ∑ k ∈ Finset.range (n + 1), if state n ((k : ℤ), 0) then 10 ^ (n - k) else 0

/-- The generating function Sum_{n >= 0} a(n) x^n. -/
noncomputable def A : ℚ⟦X⟧ := PowerSeries.mk fun n => (a n : ℚ)

/-- Barker's closed forms, recurrence and generating function. -/
theorem main :
    (∀ n : ℕ, 1 < n → Even n → (a n : ℚ) = (989 * (-10) ^ n + 991 * 10 ^ n) / 1800) ∧
    (∀ n : ℕ, 1 < n → Odd n → (a n : ℚ) = (989 * (-10) ^ n + 991 * 10 ^ n - 200) / 1800) ∧
    (∀ n : ℕ, 5 < n → (a n : ℤ) = 101 * a (n - 2) - 100 * a (n - 4)) ∧
    A = (1 + 10 * X + 9 * X ^ 2 - 1009 * X ^ 3 - 10 * X ^ 4 + 1010 * X ^ 5) *
      ((1 - X) * (1 + X) * (1 - 10 * X) * (1 + 10 * X))⁻¹ := by
  sorry

end OMA.S_oeis_a280368

import Mathlib

/-!
# OEIS A284352: Barker's closed form, recurrence and g.f. for the x-axis of the 2D Rule 899

Source: https://oeis.org/A284352 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry A284352 (Robert Price, Mar 25 2017), offset 0: Binary representation of the x-axis, from the
origin to the right edge, of the n-th stage of growth of the two-dimensional cellular automaton
defined by Rule 899, based on the 5-celled von Neumann neighborhood.
Formula section:
Conjectures from Colin Barker, Mar 26 2017:
G.f.: (1 + 9*x + x^2) / ((1 - x)*(1 - 10*x)*(1 + 10*x)).
a(n) = (-20 + 9*(-10)^n + 191*10^n)/180.
a(n) = a(n-1) + 100*a(n-2) - 100*a(n-3) for n>2.

Formalization notes:
* Rule numbering: Wolfram's outer totalistic code on the 5-celled von Neumann neighborhood, as
  CAStep in the entry's program: the new state of a cell is bit 2k + c of the rule number, where c
  is its old state and k the number of its four neighbors (x +- 1, y) and (x, y +- 1) that are ON.
* Initial condition: at stage 0 the origin is ON and every other cell of Z x Z is OFF; each stage
  applies the rule to every cell of the plane, so the background evolves with the rule (Rule 899
  turns an OFF cell with no ON neighbor ON); the entry's program evolves the same rule on a finite
  grid.
* Reading convention: a(n) writes the cells (0, 0), ..., (n, 0) of stage n (origin first) as binary
  digits and reads them as a decimal number, as the entry's program does (the middle row of the
  trimmed stage, from the center to the right edge, FromDigits).
* The statement is the conjunction of the 3 conjectures of the site's problem, in the entry's order.
  The recurrence is stated in the integers. The closed form is stated in the rationals, where every
  division is exact. The generating function is A(x) = Sum_{n >= 0} a(n) x^n in the formal power
  series ring over the rationals, and the identity is A = N * D⁻¹, where D has a nonzero constant
  term.
* Controls proved in the proof file (theorem vals): the definition gives a(n) for n = 0..15 equal to
  the entry's first 16 terms, 1, 10, 111, 1011, 11111, 101111, 1111111, 10111111, 111111111,
  1011111111, 11111111111, 101111111111, ....
-/

namespace OMA.S_oeis_a284352

open PowerSeries

/-- Rule 899: new state from the cell's state `c` and its number `k` of ON neighbors
(Wolfram's outer totalistic code: bit `2k + c` of 899). -/
def rule (c : Bool) (k : ℕ) : Bool := (899 : ℕ).testBit (2 * k + cond c 1 0)

/-- The four von Neumann neighbors. -/
def nbrs (p : ℤ × ℤ) : List (ℤ × ℤ) :=
  [(p.1 + 1, p.2), (p.1 - 1, p.2), (p.1, p.2 + 1), (p.1, p.2 - 1)]

/-- The automaton on `ℤ × ℤ`, started from the single ON cell at the origin. -/
def state : ℕ → ℤ × ℤ → Bool
  | 0, p => decide (p = (0, 0))
  | t + 1, p => rule (state t p) ((nbrs p).countP (fun q => state t q))

/-- A284352(n): the cells `(0,0), ..., (n,0)` of stage `n` (origin first) as binary digits read in base 10. -/
def a (n : ℕ) : ℕ :=
  ∑ k ∈ Finset.range (n + 1), if state n ((k : ℤ), 0) then 10 ^ (n - k) else 0

/-- The generating function Sum_{n >= 0} a(n) x^n. -/
noncomputable def A : ℚ⟦X⟧ := PowerSeries.mk fun n => (a n : ℚ)

/-- Barker's closed form, recurrence and generating function. -/
theorem main :
    A = (1 + 9 * X + X ^ 2) * ((1 - X) * (1 - 10 * X) * (1 + 10 * X))⁻¹ ∧
    (∀ n : ℕ, (a n : ℚ) = (-20 + 9 * (-10) ^ n + 191 * 10 ^ n) / 180) ∧
    (∀ n : ℕ, 2 < n → (a n : ℤ) = a (n - 1) + 100 * a (n - 2) - 100 * a (n - 3)) := by
  sorry

end OMA.S_oeis_a284352

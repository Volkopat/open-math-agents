import Mathlib

/-!
# OEIS A278760: Wu's recurrence and generating function for the x-axis of the 2D Rule 73

Source: https://oeis.org/A278760 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry A278760 (Robert Price, Nov 27 2016), offset 0: Decimal representation of the x-axis, from the
origin to the right edge, of the n-th stage of growth of the two-dimensional cellular automaton
defined by Rule 73, based on the 5-celled von Neumann neighborhood.
Formula section:
Conjectures from Chai Wah Wu, Jun 14 2020:
a(n) = 5*a(n-2) - 4*a(n-4) for n > 7.
G.f.: (-40*x^7 + 24*x^6 + 38*x^5 - 26*x^4 + 5*x^3 + x^2 + 1)/(4*x^4 - 5*x^2 + 1).

Formalization notes:
* Rule numbering: Wolfram's outer totalistic code on the 5-celled von Neumann neighborhood, as
  CAStep in the entry's program: the new state of a cell is bit 2k + c of the rule number, where c
  is its old state and k the number of its four neighbors (x +- 1, y) and (x, y +- 1) that are ON.
* Initial condition: at stage 0 the origin is ON and every other cell of Z x Z is OFF; each stage
  applies the rule to every cell of the plane, so the background evolves with the rule (Rule 73
  turns an OFF cell with no ON neighbor ON); the entry's program evolves the same rule on a finite
  grid.
* Reading convention: a(n) reads the cells (0, 0), ..., (n, 0) of stage n as a binary number, the
  origin most significant, as the entry's program does (the middle row of the trimmed stage, from
  the center to the right edge, FromDigits).
* The statement is the conjunction of the 2 conjectures of the site's problem, in the entry's order.
  The recurrence is stated in the integers. The generating function is A(x) = Sum_{n >= 0} a(n) x^n
  in the formal power series ring over the rationals, and the identity is A = N * D⁻¹, where D has a
  nonzero constant term.
* Controls proved in the proof file (theorem vals): the definition gives a(n) for n = 0..23 equal to
  the entry's first 24 terms, 1, 0, 6, 5, 0, 63, 0, 255, 0, 1023, 0, 4095, ....
-/

namespace OMA.S_oeis_a278760

open PowerSeries

/-- Rule 73: new state from the cell's state `c` and its number `k` of ON neighbors
(Wolfram's outer totalistic code: bit `2k + c` of 73). -/
def rule (c : Bool) (k : ℕ) : Bool := (73 : ℕ).testBit (2 * k + cond c 1 0)

/-- The four von Neumann neighbors. -/
def nbrs (p : ℤ × ℤ) : List (ℤ × ℤ) :=
  [(p.1 + 1, p.2), (p.1 - 1, p.2), (p.1, p.2 + 1), (p.1, p.2 - 1)]

/-- The automaton on `ℤ × ℤ`, started from the single ON cell at the origin. -/
def state : ℕ → ℤ × ℤ → Bool
  | 0, p => decide (p = (0, 0))
  | t + 1, p => rule (state t p) ((nbrs p).countP (fun q => state t q))

/-- A278760(n): the cells `(0,0), ..., (n,0)` of stage `n` (origin first) read as a binary number. -/
def a (n : ℕ) : ℕ :=
  ∑ k ∈ Finset.range (n + 1), if state n ((k : ℤ), 0) then 2 ^ (n - k) else 0

/-- The generating function Sum_{n >= 0} a(n) x^n. -/
noncomputable def A : ℚ⟦X⟧ := PowerSeries.mk fun n => (a n : ℚ)

/-- Wu's recurrence and generating function. -/
theorem main :
    (∀ n : ℕ, 7 < n → (a n : ℤ) = 5 * a (n - 2) - 4 * a (n - 4)) ∧
    A = (-40 * X ^ 7 + 24 * X ^ 6 + 38 * X ^ 5 - 26 * X ^ 4 + 5 * X ^ 3 + X ^ 2 + 1) *
      (4 * X ^ 4 - 5 * X ^ 2 + 1)⁻¹ := by
  sorry

end OMA.S_oeis_a278760

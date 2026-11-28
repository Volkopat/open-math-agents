import Mathlib

/-!
# OEIS A280412: Gutkovskiy's recurrence and g.f. and Barker's closed forms for Rule 261

Source: https://oeis.org/A280412 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry A280412 (Robert Price, Jan 02 2017), offset 0: Decimal representation of the x-axis, from the
left edge to the origin, of the n-th stage of growth of the two-dimensional cellular automaton
defined by Rule 261, based on the 5-celled von Neumann neighborhood.
Formula section:
Conjectures from Ilya Gutkovskiy, Jan 02 2017:
G.f.: (1 + 2*x - 4*x^2 + 4*x^3)/((1 - 2*x)*(1 + 2*x)*(1 - x)*(1 + x)).
a(n) = 5*a(n-2) - 4*a(n-4).
Conjectures from Colin Barker, Jan 03 2017:
a(n) = 1 for n even.
a(n) = 2^(n+1) - 2 for n odd.

Formalization notes:
* Rule numbering: Wolfram's outer totalistic code on the 5-celled von Neumann neighborhood, as
  CAStep in the entry's program: the new state of a cell is bit 2k + c of the rule number, where c
  is its old state and k the number of its four neighbors (x +- 1, y) and (x, y +- 1) that are ON.
* Initial condition: at stage 0 the origin is ON and every other cell of Z x Z is OFF; each stage
  applies the rule to every cell of the plane, so the background evolves with the rule (Rule 261
  turns an OFF cell with no ON neighbor ON); the entry's program evolves the same rule on a finite
  grid.
* Reading convention: a(n) reads the cells (-n, 0), ..., (0, 0) of stage n as a binary number, the
  left edge most significant, as the entry's program does (the middle row of the trimmed stage, from
  the left edge to the center, FromDigits).
* The statement is the conjunction of the 4 conjectures of the site's problem, in the entry's order.
  The recurrence is stated in the integers. The closed forms are stated in the rationals, where
  every division is exact. The generating function is A(x) = Sum_{n >= 0} a(n) x^n in the formal
  power series ring over the rationals, and the identity is A = N * D⁻¹, where D has a nonzero
  constant term.
* The recurrence a(n) = 5*a(n-2) - 4*a(n-4) has no stated range; it is stated for n >= 4, the first
  n for which every a(n-k) it uses is defined (offset 0).
* Controls proved in the proof file (theorem vals): the definition gives a(n) for n = 0..16 equal to
  the entry's first 17 terms, 1, 2, 1, 14, 1, 62, 1, 254, 1, 1022, 1, 4094, ....
-/

namespace OMA.S_oeis_a280412

open PowerSeries

/-- Rule 261: new state from the cell's state `c` and its number `k` of ON neighbors
(Wolfram's outer totalistic code: bit `2k + c` of 261). -/
def rule (c : Bool) (k : ℕ) : Bool := (261 : ℕ).testBit (2 * k + cond c 1 0)

/-- The four von Neumann neighbors. -/
def nbrs (p : ℤ × ℤ) : List (ℤ × ℤ) :=
  [(p.1 + 1, p.2), (p.1 - 1, p.2), (p.1, p.2 + 1), (p.1, p.2 - 1)]

/-- The automaton on `ℤ × ℤ`, started from the single ON cell at the origin. -/
def state : ℕ → ℤ × ℤ → Bool
  | 0, p => decide (p = (0, 0))
  | t + 1, p => rule (state t p) ((nbrs p).countP (fun q => state t q))

/-- A280412(n): the cells `(-n,0), ..., (0,0)` of stage `n` (left edge first) read as a binary number. -/
def a (n : ℕ) : ℕ :=
  ∑ k ∈ Finset.range (n + 1), if state n ((k : ℤ) - n, 0) then 2 ^ (n - k) else 0

/-- The generating function Sum_{n >= 0} a(n) x^n. -/
noncomputable def A : ℚ⟦X⟧ := PowerSeries.mk fun n => (a n : ℚ)

/-- Gutkovskiy's recurrence and generating function and Barker's closed forms. -/
theorem main :
    A = (1 + 2 * X - 4 * X ^ 2 + 4 * X ^ 3) * ((1 - 2 * X) * (1 + 2 * X) * (1 - X) * (1 + X))⁻¹ ∧
    (∀ n : ℕ, 3 < n → (a n : ℤ) = 5 * a (n - 2) - 4 * a (n - 4)) ∧
    (∀ n : ℕ, Even n → (a n : ℚ) = 1) ∧
    (∀ n : ℕ, Odd n → (a n : ℚ) = 2 ^ (n + 1) - 2) := by
  sorry

end OMA.S_oeis_a280412

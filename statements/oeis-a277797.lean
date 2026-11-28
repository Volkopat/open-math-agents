import Mathlib

/-!
# OEIS A277797: Barker's closed form, recurrence and g.f. for the x-axis of the 2D Rule 1

Source: https://oeis.org/A277797 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry A277797 (Robert Price, Oct 31 2016), offset 0: Binary representation of the x-axis, from the
left edge to the origin, of the n-th stage of growth of the two-dimensional cellular automaton
defined by Rule 1, based on the 5-celled von Neumann neighborhood.
Formula section:
Conjectures from Colin Barker, Nov 01 2016:
G.f.: (1 - 100*x^2 + 1100*x^3)/((1 - x)*(1 + x)*(1 - 10*x)*(1 + 10*x)).
a(n) = 101*a(n-2) - 100*a(n-4) for n>3.
a(n) = (-91+109*(-1)^n+10^(1+n)-(-1)^n*10^(1+n))/18.

Formalization notes:
* Rule numbering: Wolfram's outer totalistic code on the 5-celled von Neumann neighborhood, as
  CAStep in the entry's program: the new state of a cell is bit 2k + c of the rule number, where c
  is its old state and k the number of its four neighbors (x +- 1, y) and (x, y +- 1) that are ON.
* Initial condition: at stage 0 the origin is ON and every other cell of Z x Z is OFF; each stage
  applies the rule to every cell of the plane, so the background evolves with the rule (Rule 1 turns
  an OFF cell with no ON neighbor ON); the entry's program evolves the same rule on a finite grid.
* Reading convention: a(n) writes the cells (-n, 0), ..., (0, 0) of stage n (left edge first) as
  binary digits and reads them as a decimal number, as the entry's program does (the middle row of
  the trimmed stage, from the left edge to the center, FromDigits).
* The statement is the conjunction of the 3 conjectures of the site's problem, in the entry's order.
  The recurrence is stated in the integers. The closed form is stated in the rationals, where every
  division is exact. The generating function is A(x) = Sum_{n >= 0} a(n) x^n in the formal power
  series ring over the rationals, and the identity is A = N * D⁻¹, where D has a nonzero constant
  term.
* Controls proved in the proof file (theorem vals): the definition gives a(n) for n = 0..16 equal to
  the entry's first 17 terms, 1, 0, 1, 1100, 1, 111100, 1, 11111100, 1, 1111111100, 1, 111111111100,
  ....
-/

namespace OMA.S_oeis_a277797

open PowerSeries

/-- Rule 1: new state from the cell's state `c` and its number `k` of ON neighbors
(Wolfram's outer totalistic code: bit `2k + c` of 1). -/
def rule (c : Bool) (k : ℕ) : Bool := (1 : ℕ).testBit (2 * k + cond c 1 0)

/-- The four von Neumann neighbors. -/
def nbrs (p : ℤ × ℤ) : List (ℤ × ℤ) :=
  [(p.1 + 1, p.2), (p.1 - 1, p.2), (p.1, p.2 + 1), (p.1, p.2 - 1)]

/-- The automaton on `ℤ × ℤ`, started from the single ON cell at the origin. -/
def state : ℕ → ℤ × ℤ → Bool
  | 0, p => decide (p = (0, 0))
  | t + 1, p => rule (state t p) ((nbrs p).countP (fun q => state t q))

/-- A277797(n): the cells `(-n,0), ..., (0,0)` of stage `n` (left edge first) as binary digits read in base 10. -/
def a (n : ℕ) : ℕ :=
  ∑ k ∈ Finset.range (n + 1), if state n ((k : ℤ) - n, 0) then 10 ^ (n - k) else 0

/-- The generating function Sum_{n >= 0} a(n) x^n. -/
noncomputable def A : ℚ⟦X⟧ := PowerSeries.mk fun n => (a n : ℚ)

/-- Barker's closed form, recurrence and generating function. -/
theorem main :
    A = (1 - 100 * X ^ 2 + 1100 * X ^ 3) * ((1 - X) * (1 + X) * (1 - 10 * X) * (1 + 10 * X))⁻¹ ∧
    (∀ n : ℕ, 3 < n → (a n : ℤ) = 101 * a (n - 2) - 100 * a (n - 4)) ∧
    (∀ n : ℕ, (a n : ℚ) = (-91 + 109 * (-1) ^ n + 10 ^ (1 + n) - (-1) ^ n * 10 ^ (1 + n)) / 18) := by
  sorry

end OMA.S_oeis_a277797

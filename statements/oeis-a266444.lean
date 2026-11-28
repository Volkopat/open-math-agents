import Mathlib

/-!
# OEIS A266444: Barker's closed form, recurrence and g.f. for the middle column of Rule 25

Source: https://oeis.org/A266444 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry (Robert Price, Dec 29 2015), offset 0: Middle column of the Rule 25 elementary cellular
automaton starting with a single ON (black) cell. Data: 1, 0, 0, 0, 1, 0, 1, 0, 1, 1, 0, 0, 0, 1,
0, 1, 0, 1, ... The formula section states: Conjectures from Colin Barker, Dec 31 2015 and
Apr 16 2019: (Start) a(n) = (1-(-1)^n)/2 for n>11. a(n) = a(n-2) for n>13.
G.f.: (1-x^2+x^4+x^9-x^10-x^11+x^13) / ((1-x)*(1+x)). (End)

Formalization notes:
* Conventions (as in Wolfram's numbering and the entry's Mathematica program): the automaton runs
  on the integers, starting from one ON cell at position 0 on an all-OFF background, and the rule
  is applied to every cell, including the background, at each step; the new state of a cell is
  bit 4l + 2c + r of 25, where l, c, r are the old states of its left neighbor, itself and its
  right neighbor.
* The middle column is the cell at position 0 (the program's middle cell of row n); a(n) is 1
  when it is ON at stage n and 0 when it is OFF.
* `main` is the conjunction of the three conjectures. The closed form is stated in Q, the
  recurrence in the natural numbers (no subtraction of values), and the g.f. as
  A(x) = N(x) * D(x)^(-1) in Q[[x]] (D has constant term 1).
* Controls proved in the proof file: a(0..33), the entry's data.
-/

namespace OMA.S_oeis_a266444

open PowerSeries

/-- Rule 25 as a local map: the new state of a cell from (left, center, right). -/
def rule (l c r : Bool) : Bool := (25 : ℕ).testBit ((cond l 4 0) + (cond c 2 0) + (cond r 1 0))

/-- The configuration at time `t`, started from the single ON cell at 0. -/
def state : ℕ → ℤ → Bool
  | 0, i => decide (i = 0)
  | t + 1, i => rule (state t (i - 1)) (state t i) (state t (i + 1))

/-- A266444(n): the middle cell (position 0) of stage n, as 1 (ON) or 0 (OFF). -/
def a (n : ℕ) : ℕ := if state n 0 then 1 else 0

/-- Barker's conjectures: the closed form for n > 11, the recurrence for n > 13, and the g.f. -/
theorem main :
    (∀ n : ℕ, 11 < n → (a n : ℚ) = (1 - (-1) ^ n) / 2) ∧
    (∀ n : ℕ, 13 < n → a n = a (n - 2)) ∧
    PowerSeries.mk (fun n => (a n : ℚ)) =
      (1 - X ^ 2 + X ^ 4 + X ^ 9 - X ^ 10 - X ^ 11 + X ^ 13) * ((1 - X) * (1 + X))⁻¹ := by
  sorry

end OMA.S_oeis_a266444

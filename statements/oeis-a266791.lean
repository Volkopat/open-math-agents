import Mathlib

/-!
# OEIS A266791: Barker's closed form and g.f. for the decimal middle column of Rule 61

Source: https://oeis.org/A266791 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry (Robert Price, Jan 03 2016), offset 0: Decimal representation of the middle column of the
Rule 61 elementary cellular automaton starting with a single ON (black) cell. Data: 1, 3, 7, 14,
29, 58, 117, 234, 468, 937, 1875, 3751, 7502, ... The formula section states: Conjectures from
Colin Barker, Jan 04 2016 and Apr 18 2019: (Start) a(n) = (-(-1)^n+5627*2^(n-9)-3)/6 for n>9.
G.f.: (1+x-x^3-x^8+x^9+x^10-x^12) / ((1-x)*(1+x)*(1-2*x)). (End)

Formalization notes:
* Conventions (as in Wolfram's numbering and the entry's Mathematica program): the automaton runs
  on the integers, starting from one ON cell at position 0 on an all-OFF background, and the rule
  is applied to every cell, including the background, at each step; the new state of a cell is
  bit 4l + 2c + r of 61, where l, c, r are the old states of its left neighbor, itself and its
  right neighbor.
* The middle column is the cell at position 0; a(n) reads its states at stages 0..n as a binary
  number with stage 0 the most significant digit, as the program does (FromDigits[Take[mc, k],
  2]).
* Barker's closed form is stated in Q for n > 9 (there 2^(n-9) has a natural exponent); the g.f.
  is A(x) = Sum_{n >= 0} a(n) x^n, stated as A = N * D^(-1) in Q[[x]] (D has constant term 1).
* `main` is the conjunction of Barker's two conjectures.
* Controls proved in the proof file: a(0..15), the entry's data.
-/

namespace OMA.S_oeis_a266791

open PowerSeries

/-- Rule 61 as a local map: the new state of a cell from (left, center, right). -/
def rule (l c r : Bool) : Bool := (61 : ℕ).testBit ((cond l 4 0) + (cond c 2 0) + (cond r 1 0))

/-- The configuration at time `t`, started from the single ON cell at 0. -/
def state : ℕ → ℤ → Bool
  | 0, i => decide (i = 0)
  | t + 1, i => rule (state t (i - 1)) (state t i) (state t (i + 1))

/-- The middle column: 1 when cell 0 is ON at stage k, 0 when it is OFF. -/
def mid (k : ℕ) : ℕ := if state k 0 then 1 else 0

/-- A266791(n): the middle cells of stages 0..n read as a binary number, stage 0 most
significant. -/
def a (n : ℕ) : ℕ := ∑ k ∈ Finset.range (n + 1), mid k * 2 ^ (n - k)

/-- Barker's conjectures: the closed form for n > 9 and the g.f. -/
theorem main :
    (∀ n : ℕ, 9 < n → (a n : ℚ) = (-(-1) ^ n + 5627 * 2 ^ (n - 9) - 3) / 6) ∧
    PowerSeries.mk (fun n => (a n : ℚ)) =
      (1 + X - X ^ 3 - X ^ 8 + X ^ 9 + X ^ 10 - X ^ 12) *
        ((1 - X) * (1 + X) * (1 - 2 * X))⁻¹ := by
  sorry

end OMA.S_oeis_a266791

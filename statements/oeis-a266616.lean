import Mathlib

/-!
# A266616: Number of OFF (white) cells in the n-th iteration of the 'Rule 41' elementary cellular automaton starting with a single ON (black) cell.

Source: https://oeis.org/A266616
Credit: @clementtrecourt

The conjectures listed in the entry, all stated below as one conjunction:
* a(n) = a(n-2)+a(n-4)-a(n-6) for n>5.
* G.f.: x*(3+3*x+x^2+5*x^3-4*x^4) / ((1-x)^2*(1+x)^2*(1+x^2)).

Conventions (as in Wolfram's numbering and the OEIS program): the automaton runs on the integers, starting from one ON cell at position 0 on an all-OFF background, and the rule is applied to every cell, including the background, at each step.
Offset 0: a(n) is the number of OFF cells among positions -n..n after n steps.
The definition below reproduces every term listed in the OEIS entry. Each formula was checked against the automaton for every n up to 120.
-/

namespace OMA.S_oeis_a266616

/-- The new value of a cell under the elementary cellular automaton with Wolfram rule number
`rule`, given the old values of its left neighbour, itself and its right neighbour. -/
def ruleOut (rule : ℕ) (l c r : Bool) : Bool :=
  rule.testBit (4 * l.toNat + 2 * c.toNat + r.toNat)

/-- `cell rule t i` is the value of the cell at position `i` after `t` steps, starting from a
single ON cell at position 0 on an all-OFF background. -/
def cell (rule : ℕ) : ℕ → ℤ → Bool
  | 0 => fun i => decide (i = 0)
  | t + 1 => fun i => ruleOut rule (cell rule t (i - 1)) (cell rule t i) (cell rule t (i + 1))

/-- The number of ON cells among positions `-t..t` after `t` steps. -/
def onCount (rule t : ℕ) : ℕ :=
  ∑ j ∈ Finset.range (2 * t + 1), if cell rule t ((j : ℤ) - t) then 1 else 0

/-- A266616(n): the number of OFF cells among positions -n..n after n steps. -/
def a (n : ℕ) : ℤ :=
  (2 * n + 1 : ℤ) - onCount 41 n

open PowerSeries in
theorem main :
    (∀ n : ℕ, 6 ≤ n → (a n : ℚ) = a (n - 2) + a (n - 4) - a (n - 6)) ∧
    (PowerSeries.mk (fun n => (a n : ℚ)) * ((1 - X) ^ 2 * (1 + X) ^ 2 * (1 + X ^ 2) : PowerSeries ℚ) = X * (3 + 3 * X + X ^ 2 + 5 * X ^ 3 - 4 * X ^ 4)) := by
  sorry

end OMA.S_oeis_a266616

import Mathlib

/-!
# A267259: Number of ON (black) cells in the n-th iteration of the 'Rule 111' elementary cellular automaton starting with a single ON (black) cell.

Source: https://oeis.org/A267259
Credit: @clementtrecourt

The conjectures listed in the entry, all stated below as one conjunction:
* a(n) = (-2*(-1)^n*n+2*n+9*(-1)^n+3)/2 for n>4.
* G.f.: (1+2*x+x^2+x^3-x^5-x^6+2*x^7-x^8) / ((1-x)^2*(1+x)^2).

Conventions (as in Wolfram's numbering and the OEIS program): the automaton runs on the integers, starting from one ON cell at position 0 on an all-OFF background, and the rule is applied to every cell, including the background, at each step.
Offset 0: a(n) is the number of ON cells among positions -n..n after n steps.
The definition below reproduces every term listed in the OEIS entry. Each formula was checked against the automaton for every n up to 120.
-/

namespace OMA.S_oeis_a267259

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

/-- A267259(n): the number of ON cells among positions -n..n after n steps. -/
def a (n : ℕ) : ℤ :=
  (onCount 111 n : ℤ)

open PowerSeries in
theorem main :
    (∀ n : ℕ, 5 ≤ n → (a n : ℚ) = (-2 * (-1 : ℚ) ^ n * (n : ℚ) + 2 * (n : ℚ) + 9 * (-1 : ℚ) ^ n + 3) / 2) ∧
    (PowerSeries.mk (fun n => (a n : ℚ)) * ((1 - X) ^ 2 * (1 + X) ^ 2 : PowerSeries ℚ) = 1 + 2 * X + X ^ 2 + X ^ 3 - X ^ 5 - X ^ 6 + 2 * X ^ 7 - X ^ 8) := by
  sorry

end OMA.S_oeis_a267259

import Mathlib

/-!
# A267459: Total number of ON (black) cells after n iterations of the 'Rule 133' elementary cellular automaton starting with a single ON (black) cell.

Source: https://oeis.org/A267459
Credit: @clementtrecourt

The conjectures listed in the entry, all stated below as one conjunction:
* a(n) = (2*n^2 - 4*n + (-1)^n + 11)/4 for n > 0.
* a(n) = 2*a(n-1) - 2*a(n-3) + a(n-4) for n > 4.
* G.f.: (1-x^2+2*x^4) / ((1-x)^3*(1+x)).

Conventions (as in Wolfram's numbering and the OEIS program): the automaton runs on the integers, starting from one ON cell at position 0 on an all-OFF background, and the rule is applied to every cell, including the background, at each step.
Offset 0: a(n) is the total number of ON cells among positions -k..k after k steps, summed over 0 <= k <= n.
The definition below reproduces every term listed in the OEIS entry. Each formula was checked against the automaton for every n up to 120.
-/

namespace OMA.S_oeis_a267459

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

/-- A267459(n): the total number of ON cells among positions -k..k after k steps, summed over 0 <= k <= n. -/
def a (n : ℕ) : ℤ :=
  ∑ k ∈ Finset.range (n + 1), (onCount 133 k : ℤ)

open PowerSeries in
theorem main :
    (∀ n : ℕ, 1 ≤ n → (a n : ℚ) = (2 * (n : ℚ) ^ 2 - 4 * (n : ℚ) + (-1 : ℚ) ^ n + 11) / 4) ∧
    (∀ n : ℕ, 5 ≤ n → (a n : ℚ) = 2 * a (n - 1) - 2 * a (n - 3) + a (n - 4)) ∧
    (PowerSeries.mk (fun n => (a n : ℚ)) * ((1 - X) ^ 3 * (1 + X) : PowerSeries ℚ) = 1 - X ^ 2 + 2 * X ^ 4) := by
  sorry

end OMA.S_oeis_a267459

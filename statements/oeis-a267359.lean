import Mathlib

/-!
# A267359: Binary representation of the n-th iteration of the 'Rule 125' elementary cellular automaton starting with a single ON (black) cell.

Source: https://oeis.org/A267359
Credit: @clementtrecourt

The conjectures listed in the entry, all stated below as one conjunction:
* a(n) = 10001*a(n-2) - 10000*a(n-4) for n > 8.
* G.f.: (1 + 11*x + 1099*x^2 - 8900*x^3 + 108900*x^4 - 10990000*x^5 + 890000*x^6 + 11000000*x^7 - 1000000*x^8) / ((1 - x)*(1 + x)*(1 - 100*x)*(1 + 100*x)).

Conventions (as in Wolfram's numbering and the OEIS program): the automaton runs on the integers, starting from one ON cell at position 0 on an all-OFF background, and the rule is applied to every cell, including the background, at each step.
Offset 0: a(n) is the number whose decimal digits, read from position -n (most significant) to position n, are the states (0 or 1) of cells -n..n after n steps.
The definition below reproduces every term listed in the OEIS entry. Each formula was checked against the automaton for every n up to 120.
-/

namespace OMA.S_oeis_a267359

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

/-- A267359(n): the number whose decimal digits, read from position -n (most significant) to position n, are the states (0 or 1) of cells -n..n after n steps. -/
def a (n : ℕ) : ℤ :=
  ∑ j ∈ Finset.range (2 * n + 1), if cell 125 n ((j : ℤ) - n) then (10 : ℤ) ^ (2 * n - j) else 0

open PowerSeries in
theorem main :
    (∀ n : ℕ, 9 ≤ n → (a n : ℚ) = 10001 * a (n - 2) - 10000 * a (n - 4)) ∧
    (PowerSeries.mk (fun n => (a n : ℚ)) * ((1 - X) * (1 + X) * (1 - 100 * X) * (1 + 100 * X) : PowerSeries ℚ) = 1 + 11 * X + 1099 * X ^ 2 - 8900 * X ^ 3 + 108900 * X ^ 4 - 10990000 * X ^ 5 + 890000 * X ^ 6 + 11000000 * X ^ 7 - 1000000 * X ^ 8) := by
  sorry

end OMA.S_oeis_a267359

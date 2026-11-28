import Mathlib

/-!
# A267802: Decimal representation of the n-th iteration of the 'Rule 213' elementary cellular automaton starting with a single ON (black) cell.

Source: https://oeis.org/A267802
Credit: @clementtrecourt

The conjectures listed in the entry, all stated below as one conjunction:
* a(n) = 5*a(n-1)-4*a(n-2) for n>3.
* G.f.: (1+2*x)*(1-4*x+16*x^2) / ((1-x)*(1-4*x)).
* a(n) = 2^(2*n+1) - 13 for n>1. - _Colin Barker_, Nov 25 2016

Conventions (as in Wolfram's numbering and the OEIS program): the automaton runs on the integers, starting from one ON cell at position 0 on an all-OFF background, and the rule is applied to every cell, including the background, at each step.
Offset 0: a(n) is the number whose binary digits, read from position -n (most significant) to position n, are the states of cells -n..n after n steps.
The definition below reproduces every term listed in the OEIS entry. Each formula was checked against the automaton for every n up to 120.
-/

namespace OMA.S_oeis_a267802

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

/-- A267802(n): the number whose binary digits, read from position -n (most significant) to position n, are the states of cells -n..n after n steps. -/
def a (n : ℕ) : ℤ :=
  ∑ j ∈ Finset.range (2 * n + 1), if cell 213 n ((j : ℤ) - n) then (2 : ℤ) ^ (2 * n - j) else 0

open PowerSeries in
theorem main :
    (∀ n : ℕ, 4 ≤ n → (a n : ℚ) = 5 * a (n - 1) - 4 * a (n - 2)) ∧
    (PowerSeries.mk (fun n => (a n : ℚ)) * ((1 - X) * (1 - 4 * X) : PowerSeries ℚ) = (1 + 2 * X) * (1 - 4 * X + 16 * X ^ 2)) ∧
    (∀ n : ℕ, 2 ≤ n → (a n : ℚ) = (2 : ℚ) ^ ((2 * n) + 1) - 13) := by
  sorry

end OMA.S_oeis_a267802

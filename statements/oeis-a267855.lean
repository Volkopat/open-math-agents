import Mathlib

/-!
# A267855: Decimal representation of the n-th iteration of the 'Rule 230' elementary cellular automaton starting with a single ON (black) cell.

Source: https://oeis.org/A267855
Credit: @clementtrecourt

The conjectures listed in the entry, all stated below as one conjunction:
* a(n) = 16*a(n-2)+16*a(n-4)-256*a(n-6) for n>5.
* G.f.: (1+6*x+4*x^2+24*x^3+32*x^4-128*x^5) / ((1-2*x)*(1+2*x)*(1-4*x)*(1+4*x)*(1+4*x^2)).

Conventions (as in Wolfram's numbering and the OEIS program): the automaton runs on the integers, starting from one ON cell at position 0 on an all-OFF background, and the rule is applied to every cell, including the background, at each step.
Offset 0: a(n) is the number whose binary digits, read from position -n (most significant) to position n, are the states of cells -n..n after n steps.
The definition below reproduces every term listed in the OEIS entry. Each formula was checked against the automaton for every n up to 120.
-/

namespace OMA.S_oeis_a267855

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

/-- A267855(n): the number whose binary digits, read from position -n (most significant) to position n, are the states of cells -n..n after n steps. -/
def a (n : ℕ) : ℤ :=
  ∑ j ∈ Finset.range (2 * n + 1), if cell 230 n ((j : ℤ) - n) then (2 : ℤ) ^ (2 * n - j) else 0

open PowerSeries in
theorem main :
    (∀ n : ℕ, 6 ≤ n → (a n : ℚ) = 16 * a (n - 2) + 16 * a (n - 4) - 256 * a (n - 6)) ∧
    (PowerSeries.mk (fun n => (a n : ℚ)) * ((1 - 2 * X) * (1 + 2 * X) * (1 - 4 * X) * (1 + 4 * X) * (1 + 4 * X ^ 2) : PowerSeries ℚ) = 1 + 6 * X + 4 * X ^ 2 + 24 * X ^ 3 + 32 * X ^ 4 - 128 * X ^ 5) := by
  sorry

end OMA.S_oeis_a267855

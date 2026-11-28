import Mathlib

/-!
# A265724: Total number of OFF (white) cells after n iterations of the 'Rule 1' elementary cellular automaton starting with a single ON (black) cell.

Source: https://oeis.org/A265724
Credit: @clementtrecourt

The conjectures listed in the entry, all stated below as one conjunction:
* a(n) = 1/2*(n^2+(-1)^n*n+4*n-(-1)^n+1).
* a(n) = 1/2*(n^2+5*n) for n even.
* a(n) = 1/2*(n^2+3*n+2) for n odd.
* a(n) = a(n-1) + 2*a(n-2) - 2*a(n-3) - a(n-4) + a(n-5) for n>4.
* G.f.: x*(3+4*x-3*x^2) / ((1-x)^3*(1+x)^2).

Conventions (as in Wolfram's numbering and the OEIS program): the automaton runs on the integers, starting from one ON cell at position 0 on an all-OFF background, and the rule is applied to every cell, including the background, at each step.
Offset 0: a(n) is the total number of OFF cells among positions -k..k after k steps, summed over 0 <= k <= n.
The definition below reproduces every term listed in the OEIS entry. Each formula was checked against the automaton for every n up to 120.
-/

namespace OMA.S_oeis_a265724

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

/-- A265724(n): the total number of OFF cells among positions -k..k after k steps, summed over 0 <= k <= n. -/
def a (n : ℕ) : ℤ :=
  ∑ k ∈ Finset.range (n + 1), ((2 * k + 1 : ℤ) - onCount 1 k)

open PowerSeries in
theorem main :
    (∀ n : ℕ, (a n : ℚ) = 1 / 2 * ((n : ℚ) ^ 2 + (-1 : ℚ) ^ n * (n : ℚ) + 4 * (n : ℚ) - (-1 : ℚ) ^ n + 1)) ∧
    (∀ n : ℕ, Even n → (a n : ℚ) = 1 / 2 * ((n : ℚ) ^ 2 + 5 * (n : ℚ))) ∧
    (∀ n : ℕ, Odd n → (a n : ℚ) = 1 / 2 * ((n : ℚ) ^ 2 + 3 * (n : ℚ) + 2)) ∧
    (∀ n : ℕ, 5 ≤ n → (a n : ℚ) = a (n - 1) + 2 * a (n - 2) - 2 * a (n - 3) - a (n - 4) + a (n - 5)) ∧
    (PowerSeries.mk (fun n => (a n : ℚ)) * ((1 - X) ^ 3 * (1 + X) ^ 2 : PowerSeries ℚ) = X * (3 + 4 * X - 3 * X ^ 2)) := by
  sorry

end OMA.S_oeis_a265724

import Mathlib

/-!
# OEIS A267270: Keller's closed forms for the binary rows of Rule 115

Source: https://oeis.org/A267270 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry (Robert Price, Jan 12 2016), offset 0: Binary representation of the n-th iteration of the
Rule 115 elementary cellular automaton starting with a single ON (black) cell. Data: 1, 101, 1100,
1101111, 1100000, 11101111111, 1100000000, 111101111111111, ...
The formula section states: Conjecture: a(n) = (10^(2*n + 1) - 9*10^(3*n/2 - 1/2) - 1)/9 for odd
n; a(n) = 1100*10^(3*n/2 - 3) for even n > 0. - Karl V. Keller, Jr., Apr 02 2022

Formalization notes:
* Conventions (as in Wolfram's numbering and the entry's Mathematica program): the automaton runs
  on the integers, starting from one ON cell at position 0 on an all-OFF background, and the rule
  is applied to every cell, including the background, at each step; the new state of a cell is
  bit 4l + 2c + r of 115, where l, c, r are the old states of its left neighbor, itself and its
  right neighbor. Rule 115 turns the background ON at odd steps.
* a(n) writes the cells -n..n of stage n as binary digits, leftmost cell first, and reads that
  string in base 10, as the entry's program does (Take the middle 2n+1 cells, FromDigits with the
  default base 10).
* The exponents are integers on the stated parities: for odd n, 3n/2 - 1/2 = (3n - 1)/2, written
  with natural-number division of the even number 3n - 1; for even n > 0, 3n/2 - 3 is written
  3n/2 - 3 with exact natural-number division and subtraction (3n/2 >= 3). The odd-n formula is
  stated in Q, where the division by 9 is exact anyway.
* `main` is the conjunction of Keller's two formulas (the site's problem; the entry's Empirical
  g.f. is also proved in the proof file, theorem barker).
* Controls proved in the proof file: a(0..19), the entry's data.
-/

namespace OMA.S_oeis_a267270

open PowerSeries

/-- Rule 115 as a local map: the new state of a cell from (left, center, right). -/
def rule (l c r : Bool) : Bool := (115 : ℕ).testBit ((cond l 4 0) + (cond c 2 0) + (cond r 1 0))

/-- The configuration at time `t`, started from the single ON cell at 0. -/
def state : ℕ → ℤ → Bool
  | 0, i => decide (i = 0)
  | t + 1, i => rule (state t (i - 1)) (state t i) (state t (i + 1))

/-- A267270(n): row `n`, cells `-n..n` (leftmost first), written as binary digits and read in
base 10. -/
def a (n : ℕ) : ℕ :=
  ∑ k ∈ Finset.range (2 * n + 1), if state n ((k : ℤ) - n) then 10 ^ (2 * n - k) else 0

/-- Keller's conjecture: the closed forms for odd n and for even n > 0. -/
theorem main :
    (∀ n : ℕ, Odd n → (a n : ℚ) = (10 ^ (2 * n + 1) - 9 * 10 ^ ((3 * n - 1) / 2) - 1) / 9) ∧
    (∀ n : ℕ, Even n → 0 < n → a n = 1100 * 10 ^ (3 * n / 2 - 3)) := by
  sorry

end OMA.S_oeis_a267270

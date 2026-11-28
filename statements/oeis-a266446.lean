import Mathlib

/-!
# OEIS A266446: Barker's and Keller's formulas for the decimal middle column of Rule 25

Source: https://oeis.org/A266446 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry (Robert Price, Dec 29 2015), offset 0: Decimal representation of the middle column of the
Rule 25 elementary cellular automaton starting with a single ON (black) cell. Data: 1, 2, 4, 8,
17, 34, 69, 138, 277, 555, 1110, 2220, 4440, 8881, 17762, 35525, 71050, ...
The formula section states: Conjectures from Colin Barker, Dec 30 2015 and Apr 16 2019: (Start)
a(n) = (-(-1)^n+6661*2^(n-10)-3)/6 for n>10.
G.f.: (1-x^2+x^4+x^9-x^10-x^11+x^13) / ((1-x)*(1+x)*(1-2*x)). (End)
Conjecture: a(n) = floor(6661*2^n/6144). - Karl V. Keller, Jr., Dec 26 2021

Formalization notes:
* Conventions (as in Wolfram's numbering and the entry's Mathematica program): the automaton runs
  on the integers, starting from one ON cell at position 0 on an all-OFF background, and the rule
  is applied to every cell, including the background, at each step; the new state of a cell is
  bit 4l + 2c + r of 25, where l, c, r are the old states of its left neighbor, itself and its
  right neighbor.
* The middle column is the cell at position 0; a(n) reads its states at stages 0..n as a binary
  number with stage 0 the most significant digit, as the program does (FromDigits[Take[mc, k],
  2]).
* Barker's closed form is stated in Q for n > 10 (there 2^(n-10) has a natural exponent); the
  g.f. is A(x) = Sum_{n >= 0} a(n) x^n, stated as A = N * D^(-1) in Q[[x]] (D has constant
  term 1); Keller's formula is stated for every n >= 0 with floor written as division in the
  natural numbers.
* `main` is the conjunction of the three conjectures.
* Controls proved in the proof file: a(0..16), the entry's data.
-/

namespace OMA.S_oeis_a266446

open PowerSeries

/-- Rule 25 as a local map: the new state of a cell from (left, center, right). -/
def rule (l c r : Bool) : Bool := (25 : ℕ).testBit ((cond l 4 0) + (cond c 2 0) + (cond r 1 0))

/-- The configuration at time `t`, started from the single ON cell at 0. -/
def state : ℕ → ℤ → Bool
  | 0, i => decide (i = 0)
  | t + 1, i => rule (state t (i - 1)) (state t i) (state t (i + 1))

/-- The middle column: 1 when cell 0 is ON at stage k, 0 when it is OFF. -/
def mid (k : ℕ) : ℕ := if state k 0 then 1 else 0

/-- A266446(n): the middle cells of stages 0..n read as a binary number, stage 0 most
significant. -/
def a (n : ℕ) : ℕ := ∑ k ∈ Finset.range (n + 1), mid k * 2 ^ (n - k)

/-- Barker's closed form (n > 10) and g.f., and Keller's floor formula. -/
theorem main :
    (∀ n : ℕ, 10 < n → (a n : ℚ) = (-(-1) ^ n + 6661 * 2 ^ (n - 10) - 3) / 6) ∧
    PowerSeries.mk (fun n => (a n : ℚ)) =
      (1 - X ^ 2 + X ^ 4 + X ^ 9 - X ^ 10 - X ^ 11 + X ^ 13) *
        ((1 - X) * (1 + X) * (1 - 2 * X))⁻¹ ∧
    ∀ n : ℕ, a n = 6661 * 2 ^ n / 6144 := by
  sorry

end OMA.S_oeis_a266446

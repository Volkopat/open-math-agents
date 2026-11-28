import Mathlib

/-!
# OEIS A266445: Barker's and Keller's formulas for the binary middle column of Rule 25

Source: https://oeis.org/A266445 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry (Robert Price, Dec 29 2015), offset 0: Binary representation of the middle column of the
Rule 25 elementary cellular automaton starting with a single ON (black) cell. Data: 1, 10, 100,
1000, 10001, 100010, 1000101, 10001010, 100010101, 1000101011, 10001010110, ...
The formula section states: Conjectures from Colin Barker, Dec 31 2015 and Apr 16 2019: (Start)
a(n) = (-9*(-1)^n+9901000008901*2^(n-10)*5^(n-11)-11)/198 for n>10.
G.f.: (1-x^2+x^4+x^9-x^10-x^11+x^13) / ((1-x)*(1+x)*(1-10*x)). (End)
Conjecture: a(n) = floor(9901000008901*10^n/9900000000000). - Karl V. Keller, Jr., Jan 30 2022

Formalization notes:
* Conventions (as in Wolfram's numbering and the entry's Mathematica program): the automaton runs
  on the integers, starting from one ON cell at position 0 on an all-OFF background, and the rule
  is applied to every cell, including the background, at each step; the new state of a cell is
  bit 4l + 2c + r of 25, where l, c, r are the old states of its left neighbor, itself and its
  right neighbor.
* The middle column is the cell at position 0; a(n) writes its states at stages 0..n as a string
  of binary digits, stage 0 first, and reads that string in base 10, as the program does
  (FromDigits[Take[mc, k]], base 10 by default).
* Barker's closed form is stated in Q for n > 10 (there both exponents are natural); the g.f. is
  A(x) = Sum_{n >= 0} a(n) x^n, stated as A = N * D^(-1) in Q[[x]] (D has constant term 1);
  Keller's formula is stated for every n >= 0 with floor written as division in the natural
  numbers.
* `main` is the conjunction of the three conjectures.
* Controls proved in the proof file: a(0..19), the entry's data.
-/

namespace OMA.S_oeis_a266445

open PowerSeries

/-- Rule 25 as a local map: the new state of a cell from (left, center, right). -/
def rule (l c r : Bool) : Bool := (25 : ℕ).testBit ((cond l 4 0) + (cond c 2 0) + (cond r 1 0))

/-- The configuration at time `t`, started from the single ON cell at 0. -/
def state : ℕ → ℤ → Bool
  | 0, i => decide (i = 0)
  | t + 1, i => rule (state t (i - 1)) (state t i) (state t (i + 1))

/-- The middle column: 1 when cell 0 is ON at stage k, 0 when it is OFF. -/
def mid (k : ℕ) : ℕ := if state k 0 then 1 else 0

/-- A266445(n): the middle cells of stages 0..n written as a string of binary digits, stage 0
first, and read in base 10. -/
def a (n : ℕ) : ℕ := ∑ k ∈ Finset.range (n + 1), mid k * 10 ^ (n - k)

/-- Barker's closed form (n > 10) and g.f., and Keller's floor formula. -/
theorem main :
    (∀ n : ℕ, 10 < n →
      (a n : ℚ) = (-9 * (-1) ^ n + 9901000008901 * 2 ^ (n - 10) * 5 ^ (n - 11) - 11) / 198) ∧
    PowerSeries.mk (fun n => (a n : ℚ)) =
      (1 - X ^ 2 + X ^ 4 + X ^ 9 - X ^ 10 - X ^ 11 + X ^ 13) *
        ((1 - X) * (1 + X) * (1 - 10 * X))⁻¹ ∧
    ∀ n : ℕ, a n = 9901000008901 * 10 ^ n / 9900000000000 := by
  sorry

end OMA.S_oeis_a266445

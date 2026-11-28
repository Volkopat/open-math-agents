import Mathlib

/-!
# OEIS A266671: Barker's recurrence and generating function for the decimal rows of Rule 53

Source: https://oeis.org/A266671 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry (Robert Price, Jan 02 2016), offset 0: Decimal representation of the n-th iteration of the
Rule 53 elementary cellular automaton starting with a single ON (black) cell. Data: 1, 3, 8, 95,
64, 1791, 512, 30719, ... The formula section states: Conjectures from Colin Barker, Jan 03 2016
and Apr 18 2019: (Start) a(n) = 25*a(n-2) - 152*a(n-4) + 128*a(n-6) for n>5. G.f.:
(1+3*x-17*x^2+20*x^3+16*x^4-128*x^5) / ((1-x)*(1+x)*(1-4*x)*(1+4*x)*(1-8*x^2)). (End)

Formalization notes:
* Conventions (as in Wolfram's numbering and the entry's Mathematica program): the automaton runs
  on the integers, starting from one ON cell at position 0 on an all-OFF background, and the rule
  is applied to every cell, including the background, at each step; the new state of a cell is bit
  4l + 2c + r of 53, where l, c, r are the old states of its left neighbor, itself and its right
  neighbor. Rule 53 turns the background ON at odd steps.
* a(n) is the binary value of the cells -n..n (leftmost cell most significant), as the entry's
  program does (Take the middle 2n+1 cells, FromDigits base 2).
* The recurrence is stated in the integers for every n > 5; the g.f. is A(x) = Sum_{n >= 0} a(n)
  x^n (offset 0), stated as A = N * D^(-1) in Q[[x]] (D has constant term 1).
* `main` is the conjunction of Barker's two conjectures.
* Controls proved in the proof file: a(0..19), the entry's data.
-/

namespace OMA.S_oeis_a266671

open PowerSeries

/-- Rule 53 as a local map: the new state of a cell from (left, center, right). -/
def rule (l c r : Bool) : Bool := (53 : ℕ).testBit ((cond l 4 0) + (cond c 2 0) + (cond r 1 0))

/-- The configuration at time `t`, started from the single ON cell at 0. -/
def state : ℕ → ℤ → Bool
  | 0, i => decide (i = 0)
  | t + 1, i => rule (state t (i - 1)) (state t i) (state t (i + 1))

/-- A266671(n): row `n`, cells `-n..n` (leftmost first), read as a binary number. -/
def a (n : ℕ) : ℕ :=
  ∑ k ∈ Finset.range (2 * n + 1), if state n ((k : ℤ) - n) then 2 ^ (2 * n - k) else 0

/-- Barker's conjectures: the recurrence and the g.f. -/
theorem main :
    (∀ n : ℕ, 5 < n →
      (a n : ℤ) = 25 * a (n - 2) - 152 * a (n - 4) + 128 * a (n - 6)) ∧
    PowerSeries.mk (fun n => (a n : ℚ)) =
      (1 + 3 * X - 17 * X ^ 2 + 20 * X ^ 3 + 16 * X ^ 4 - 128 * X ^ 5) *
        ((1 - X) * (1 + X) * (1 - 4 * X) * (1 + 4 * X) * (1 - 8 * X ^ 2))⁻¹ := by
  sorry

end OMA.S_oeis_a266671

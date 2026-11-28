import Mathlib

/-!
# OEIS A267139: Barker's recurrence and generating function for the decimal rows of Rule 103

Source: https://oeis.org/A267139 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry (Robert Price, Jan 10 2016), offset 0: Decimal representation of the n-th iteration of the
Rule 103 elementary cellular automaton starting with a single ON (black) cell. Data: 1, 6, 6,
117, 60, 1931, 376, 32535, 752, 523823, 1504, 8387679, 3008, 134215871, ...
The formula section states: Conjectures from Colin Barker, Jan 11 2016 and Apr 19 2019: (Start)
a(n) = 19*a(n-2) - 50*a(n-4) + 32*a(n-6) for n > 10.
G.f.: (1 + 6*x - 13*x^2 + 3*x^3 - 4*x^4 + 8*x^5 - 496*x^6 + 1504*x^7 - 3584*x^8 - 1536*x^9 +
4096*x^10) / ((1-x)*(1+x)*(1-4*x)*(1+4*x)*(1-2*x^2)). (End)

Formalization notes:
* Conventions (as in Wolfram's numbering and the entry's Mathematica program): the automaton runs
  on the integers, starting from one ON cell at position 0 on an all-OFF background, and the rule
  is applied to every cell, including the background, at each step; the new state of a cell is
  bit 4l + 2c + r of 103, where l, c, r are the old states of its left neighbor, itself and its
  right neighbor. Rule 103 turns the background ON at odd steps.
* a(n) reads the cells -n..n of stage n as a binary number with the leftmost cell most
  significant, as the entry's program does (Take the middle 2n+1 cells, FromDigits base 2).
* The recurrence is stated in the integers for every n > 10; the g.f. is
  A(x) = Sum_{n >= 0} a(n) x^n (offset 0), stated as A = N * D^(-1) in Q[[x]] (D has constant
  term 1).
* `main` is the conjunction of Barker's two conjectures.
* Controls proved in the proof file: a(0..13) = 1, 6, 6, 117, 60, 1931, 376, 32535, 752, 523823,
  1504, 8387679, 3008, 134215871, as in the entry.
-/

namespace OMA.S_oeis_a267139

open PowerSeries

/-- Rule 103 as a local map: the new state of a cell from (left, center, right). -/
def rule (l c r : Bool) : Bool := (103 : ℕ).testBit ((cond l 4 0) + (cond c 2 0) + (cond r 1 0))

/-- The configuration at time `t`, started from the single ON cell at 0. -/
def state : ℕ → ℤ → Bool
  | 0, i => decide (i = 0)
  | t + 1, i => rule (state t (i - 1)) (state t i) (state t (i + 1))

/-- A267139(n): row `n`, cells `-n..n` (leftmost first), read as a binary number. -/
def a (n : ℕ) : ℕ :=
  ∑ k ∈ Finset.range (2 * n + 1), if state n ((k : ℤ) - n) then 2 ^ (2 * n - k) else 0

/-- Barker's conjectures: the recurrence for n > 10 and the g.f. -/
theorem main :
    (∀ n : ℕ, 10 < n → (a n : ℤ) = 19 * a (n - 2) - 50 * a (n - 4) + 32 * a (n - 6)) ∧
    PowerSeries.mk (fun n => (a n : ℚ)) =
      (1 + 6 * X - 13 * X ^ 2 + 3 * X ^ 3 - 4 * X ^ 4 + 8 * X ^ 5 - 496 * X ^ 6 + 1504 * X ^ 7 -
        3584 * X ^ 8 - 1536 * X ^ 9 + 4096 * X ^ 10) *
        ((1 - X) * (1 + X) * (1 - 4 * X) * (1 + 4 * X) * (1 - 2 * X ^ 2))⁻¹ := by
  sorry

end OMA.S_oeis_a267139

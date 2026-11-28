import Mathlib

/-!
# OEIS A266787: Barker's recurrence and generating function for the binary rows of Rule 61

Source: https://oeis.org/A266787 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry (Robert Price, Jan 03 2016), offset 0: Binary representation of the n-th iteration of the
Rule 61 elementary cellular automaton starting with a single ON (black) cell. Data: 1, 11, 1100,
1010111, 1111000, 11010001111, 1111010000, 111010001111111, ... The formula section states:
Conjectures from Colin Barker, Jan 03 2016 and Apr 18 2019: (Start) a(n) =
11001*a(n-2)-10011000*a(n-4)+10000000*a(n-6) for n>10. G.f.: (1 +11*x -9901*x^2 +889100*x^3
-979100*x^4 +7891000*x^5 -109001000*x^6 +1090110000*x^7 +9990000*x^8 -1100000000*x^9
+100000000*x^10) / ((1 -x)*(1 +x)*(1 -100*x)*(1 +100*x)*(1 -1000*x^2)). (End)

Formalization notes:
* Conventions (as in Wolfram's numbering and the entry's Mathematica program): the automaton runs
  on the integers, starting from one ON cell at position 0 on an all-OFF background, and the rule
  is applied to every cell, including the background, at each step; the new state of a cell is bit
  4l + 2c + r of 61, where l, c, r are the old states of its left neighbor, itself and its right
  neighbor. Rule 61 turns the background ON at odd steps.
* a(n) is the cells -n..n written as binary digits (leftmost first) and read in base 10, as the
  entry's program does (Take the middle 2n+1 cells, FromDigits with the default base 10).
* The recurrence is stated in the integers for every n > 10; the g.f. is A(x) = Sum_{n >= 0} a(n)
  x^n (offset 0), stated as A = N * D^(-1) in Q[[x]] (D has constant term 1).
* `main` is the conjunction of Barker's two conjectures.
* Controls proved in the proof file: a(0..15), the entry's data.
-/

namespace OMA.S_oeis_a266787

open PowerSeries

/-- Rule 61 as a local map: the new state of a cell from (left, center, right). -/
def rule (l c r : Bool) : Bool := (61 : ℕ).testBit ((cond l 4 0) + (cond c 2 0) + (cond r 1 0))

/-- The configuration at time `t`, started from the single ON cell at 0. -/
def state : ℕ → ℤ → Bool
  | 0, i => decide (i = 0)
  | t + 1, i => rule (state t (i - 1)) (state t i) (state t (i + 1))

/-- A266787(n): row `n`, cells `-n..n` (leftmost first), written as binary digits and read in
base 10. -/
def a (n : ℕ) : ℕ :=
  ∑ k ∈ Finset.range (2 * n + 1), if state n ((k : ℤ) - n) then 10 ^ (2 * n - k) else 0

/-- Barker's conjectures: the recurrence and the g.f. -/
theorem main :
    (∀ n : ℕ, 10 < n →
      (a n : ℤ) = 11001 * a (n - 2) - 10011000 * a (n - 4) + 10000000 * a (n - 6)) ∧
    PowerSeries.mk (fun n => (a n : ℚ)) =
      (1 + 11 * X - 9901 * X ^ 2 + 889100 * X ^ 3 - 979100 * X ^ 4 + 7891000 * X ^ 5 - 109001000 * X ^ 6 + 1090110000 * X ^ 7 + 9990000 * X ^ 8 - 1100000000 * X ^ 9 + 100000000 * X ^ 10) *
        ((1 - X) * (1 + X) * (1 - 100 * X) * (1 + 100 * X) * (1 - 1000 * X ^ 2))⁻¹ := by
  sorry

end OMA.S_oeis_a266787

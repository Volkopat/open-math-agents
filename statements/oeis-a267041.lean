import Mathlib

/-!
# OEIS A267041: Barker's recurrence and g.f. for the rows of Rule 91

Source: https://oeis.org/A267041 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry (Robert Price, Jan 09 2016), offset 0: Binary representation of the n-th iteration of the
'Rule 91' elementary cellular automaton starting with a single ON (black) cell. The formula section
states: Conjectures from Colin Barker, Jan 10 2016: (Start) a(n) =
10101*a(n-2)-1010100*a(n-4)+1000000*a(n-6) for n>8. G.f.: (1 +101*x-9091*x^2 +79810*x^3
-8080810*x^4 +100810100*x^5 -10092910100*x^6 -101000000*x^7 +10101000000*x^8) / ((1 -x)*(1 +x)*(1
-10*x)*(1 +10*x)*(1 -100*x)*(1 +100*x)). (End)

Formalization notes:
* Conventions (as in Wolfram's numbering and the entry's Mathematica program): the automaton runs
  on the integers, starting from one ON cell at position 0 on an all-OFF background, and the rule
  is applied to every cell, including the background, at each step; the new state of a cell is
  bit 4l + 2c + r of 91, where l, c, r are the old states of its left neighbor, itself and its
  right neighbor.
* a(n) is the cells at positions -n..n after n steps, read as the digits of a number in base 10
  (leftmost cell most significant).
* `main` is the conjunction of both conjectures. The g.f. is stated as A(x) = N(x) * D(x)^(-1) in
  Q[[x]] (D has constant term 1).
* Controls: the definitions give a(0..8) = 1, 101, 1010, 1100011, 1111100, 11110001111, 111110000,
  111111000111111, 11111000000, as in the entry.
-/

namespace OMA.S_oeis_a267041

/-- Rule 91 as a local map: the new state of a cell from (left, centre, right). -/
def rule (l c r : Bool) : Bool := (91 : ℕ).testBit ((cond l 4 0) + (cond c 2 0) + (cond r 1 0))

/-- The configuration at time `t`, started from the single ON cell at 0. -/
def state : ℕ → ℤ → Bool
  | 0, i => decide (i = 0)
  | t + 1, i => rule (state t (i - 1)) (state t i) (state t (i + 1))

/-- A267041(n): row `n`, cells `-n..n` (leftmost = most significant), in base 10. -/
def a (n : ℕ) : ℕ :=
  ∑ k ∈ Finset.range (2 * n + 1), if state n ((k : ℤ) - n) then 10 ^ (2 * n - k) else 0

open PowerSeries in
/-- Barker's conjectures: the recurrence for n > 8, and the g.f. -/
theorem main :
    (∀ n : ℕ, 8 < n →
      (a n : ℤ) = 10101 * a (n - 2) - 1010100 * a (n - 4) + 1000000 * a (n - 6)) ∧
    PowerSeries.mk (fun n => (a n : ℚ)) =
      (1 + 101 * X - 9091 * X ^ 2 + 79810 * X ^ 3 - 8080810 * X ^ 4 + 100810100 * X ^ 5
        - 10092910100 * X ^ 6 - 101000000 * X ^ 7 + 10101000000 * X ^ 8) *
      ((1 - X) * (1 + X) * (1 - 10 * X) * (1 + 10 * X) * (1 - 100 * X) * (1 + 100 * X))⁻¹ := by
  sorry

end OMA.S_oeis_a267041

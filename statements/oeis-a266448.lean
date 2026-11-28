import Mathlib

/-!
# OEIS A266448: Barker's closed form, recurrence and g.f. for the total ON cells of Rule 25

Source: https://oeis.org/A266448 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry (Robert Price, Dec 29 2015), offset 0: Total number of ON (black) cells after n iterations
of the Rule 25 elementary cellular automaton starting with a single ON (black) cell. Data: 1, 2,
4, 7, 11, 17, 21, 31, 35, 49, 53, 71, 75, 97, 101, ... The formula section states: Conjectures
from Colin Barker, Dec 30 2015 and Apr 16 2019: (Start) a(n) = (2*n^2+2*n+(-1)^n*(7-2*n)+5)/4
for n>2. a(n) = a(n-1)+2*a(n-2)-2*a(n-3)-a(n-4)+a(n-5) for n>7.
G.f.: (1+x+x^3+x^4+x^5-2*x^6+x^7) / ((1-x)^3*(1+x)^2). (End)

Formalization notes:
* Conventions (as in Wolfram's numbering and the entry's Mathematica program): the automaton runs
  on the integers, starting from one ON cell at position 0 on an all-OFF background, and the rule
  is applied to every cell, including the background, at each step; the new state of a cell is
  bit 4l + 2c + r of 25, where l, c, r are the old states of its left neighbor, itself and its
  right neighbor.
* Rule 25 turns the background ON at odd steps, so the cells of stage t are counted where the
  program counts them, among positions -t..t; a(n) is the sum of these counts over the stages
  0..n (the program's Total[Take[nbc, k]]).
* `main` is the conjunction of the three conjectures. The closed form is stated in Q, the
  recurrence in the integers, and the g.f. as A(x) = N(x) * D(x)^(-1) in Q[[x]] (D has constant
  term 1).
* Controls proved in the proof file: a(0..20) = 1, 2, 4, 7, 11, 17, 21, 31, 35, 49, 53, 71, 75,
  97, 101, 127, 131, 161, 165, 199, 203, as in the entry.
-/

namespace OMA.S_oeis_a266448

open PowerSeries

/-- Rule 25 as a local map: the new state of a cell from (left, center, right). -/
def rule (l c r : Bool) : Bool := (25 : ℕ).testBit ((cond l 4 0) + (cond c 2 0) + (cond r 1 0))

/-- The configuration at time `t`, started from the single ON cell at 0. -/
def state : ℕ → ℤ → Bool
  | 0, i => decide (i = 0)
  | t + 1, i => rule (state t (i - 1)) (state t i) (state t (i + 1))

/-- ON cells among positions `-t..t` at time `t`. -/
noncomputable def cnt (t : ℕ) : ℕ := ((Finset.Icc (-(t : ℤ)) t).filter (fun i => state t i)).card

/-- A266448(n): the total number of ON cells in stages 0..n, each stage counted on `-t..t`. -/
noncomputable def a (n : ℕ) : ℕ := ∑ t ∈ Finset.range (n + 1), cnt t

/-- Barker's conjectures: the closed form for n > 2, the recurrence for n > 7, and the g.f. -/
theorem main :
    (∀ n : ℕ, 2 < n → (a n : ℚ) = (2 * n ^ 2 + 2 * n + (-1) ^ n * (7 - 2 * n) + 5) / 4) ∧
    (∀ n : ℕ, 7 < n →
      (a n : ℤ) = a (n - 1) + 2 * a (n - 2) - 2 * a (n - 3) - a (n - 4) + a (n - 5)) ∧
    PowerSeries.mk (fun n => (a n : ℚ)) =
      (1 + X + X ^ 3 + X ^ 4 + X ^ 5 - 2 * X ^ 6 + X ^ 7) * ((1 - X) ^ 3 * (1 + X) ^ 2)⁻¹ := by
  sorry

end OMA.S_oeis_a266448

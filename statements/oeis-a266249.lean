import Mathlib

/-!
# OEIS A266249: Barker's closed form, recurrence and g.f. for the ON cells of Rule 9

Source: https://oeis.org/A266249 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry (Robert Price, Dec 25 2015), offset 0: Number of ON (black) cells in the n-th iteration of
the 'Rule 9' elementary cellular automaton starting with a single ON (black) cell. The formula
section states: Conjectures from Colin Barker, Dec 28 2015 and Apr 14 2019: (Start) a(n) =
(-2*(-1)^n*n+2*n+9*(-1)^n-1)/2 for n>3. a(n) = 2*a(n-2)-a(n-4) for n>7. G.f.:
(1+2*x^3+x^4+x^5-2*x^6+x^7) / ((1-x)^2*(1+x)^2). (End)

Formalization notes:
* Conventions (as in Wolfram's numbering and the entry's Mathematica program): the automaton runs
  on the integers, starting from one ON cell at position 0 on an all-OFF background, and the rule
  is applied to every cell, including the background, at each step; the new state of a cell is
  bit 4l + 2c + r of 9, where l, c, r are the old states of its left neighbor, itself and its
  right neighbor.
* Rule 9 turns the background ON, so the cells are counted where the program counts them: a(n) is
  the number of ON cells among positions -n..n after n steps.
* `main` is the conjunction of the three conjectures. The closed form is stated in Q, the
  recurrence in the integers, and the g.f. as A(x) = N(x) * D(x)^(-1) in Q[[x]] (D has constant
  term 1).
* Controls: the definitions give a(0..7) = 1, 0, 2, 2, 4, 5, 4, 9, as in the entry.
-/

namespace OMA.S_oeis_a266249

/-- Rule 9 as a local map: the new state of a cell from (left, centre, right). -/
def rule (l c r : Bool) : Bool := (9 : ℕ).testBit ((cond l 4 0) + (cond c 2 0) + (cond r 1 0))

/-- The configuration at time `t`, started from the single ON cell at 0. -/
def state : ℕ → ℤ → Bool
  | 0, i => decide (i = 0)
  | t + 1, i => rule (state t (i - 1)) (state t i) (state t (i + 1))

/-- A266249(n): ON cells among positions `-n..n` at time `n`. -/
noncomputable def a (n : ℕ) : ℕ := ((Finset.Icc (-(n : ℤ)) n).filter (fun i => state n i)).card

open PowerSeries in
/-- Barker's conjectures: the closed form for n > 3, the recurrence for n > 7, and the g.f. -/
theorem main :
    (∀ n : ℕ, 3 < n → (a n : ℚ) = (-2 * (-1) ^ n * n + 2 * n + 9 * (-1) ^ n - 1) / 2) ∧
    (∀ n : ℕ, 7 < n → (a n : ℤ) = 2 * a (n - 2) - a (n - 4)) ∧
    PowerSeries.mk (fun n => (a n : ℚ)) =
      (1 + 2 * X ^ 3 + X ^ 4 + X ^ 5 - 2 * X ^ 6 + X ^ 7) * ((1 - X) ^ 2 * (1 + X) ^ 2)⁻¹ := by
  sorry

end OMA.S_oeis_a266249

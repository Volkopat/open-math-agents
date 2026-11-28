import Mathlib

/-!
# OEIS A265430: Barker's closed form, recurrence and g.f. for the OFF cells of Rule 188

Source: https://oeis.org/A265430 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry (Robert Price, Dec 08 2015), offset 0: Number of OFF (white) cells in the n-th iteration of
the 'Rule 188' elementary cellular automaton starting with a single ON (black) cell. The formula
section states: Conjectures from Colin Barker, Dec 09 2015 and Apr 16 2019: (Start) a(n) =
1/8*(10*n+3*(-1)^n-(1-i)*(-i)^n-(1+i)*i^n-1) where i = sqrt(-1). a(n) = a(n-1) + a(n-4) - a(n-5)
for n>4. G.f.: x*(1+2*x+2*x^3) / ((1-x)^2*(1+x)*(1+x^2)). (End)

Formalization notes:
* Conventions (as in Wolfram's numbering and the entry's Mathematica program): the automaton runs
  on the integers, starting from one ON cell at position 0 on an all-OFF background, and the rule
  is applied to every cell, including the background, at each step; the new state of a cell is
  bit 4l + 2c + r of 188, where l, c, r are the old states of its left neighbor, itself and its
  right neighbor.
* As in the program, a(n) is the number of OFF cells among positions -n..n after n steps.
* `main` is the conjunction of the three conjectures. The closed form has no stated range and is
  stated in C for every n >= 0, with i the imaginary unit; the recurrence is stated in the
  integers, and the g.f. as A(x) = N(x) * D(x)^(-1) in Q[[x]] (D has constant term 1).
* Controls: the definitions give a(0..4) = 0, 1, 3, 3, 5, as in the entry.
-/

namespace OMA.S_oeis_a265430

/-- Rule 188 as a local map: the new state of a cell from (left, centre, right). -/
def rule (l c r : Bool) : Bool := (188 : ℕ).testBit ((cond l 4 0) + (cond c 2 0) + (cond r 1 0))

/-- The configuration at time `t`, started from the single ON cell at 0. -/
def state : ℕ → ℤ → Bool
  | 0, i => decide (i = 0)
  | t + 1, i => rule (state t (i - 1)) (state t i) (state t (i + 1))

/-- A265430(n): OFF cells among positions `-n..n` at time `n`. -/
noncomputable def a (n : ℕ) : ℕ :=
  ((Finset.Icc (-(n : ℤ)) n).filter (fun i => state n i = false)).card

open PowerSeries in
/-- Barker's conjectures: the closed form, the recurrence for n > 4, and the g.f. -/
theorem main :
    (∀ n : ℕ, (a n : ℂ) = (10 * n + 3 * (-1) ^ n - (1 - Complex.I) * (-Complex.I) ^ n
      - (1 + Complex.I) * Complex.I ^ n - 1) / 8) ∧
    (∀ n : ℕ, 4 < n → (a n : ℤ) = a (n - 1) + a (n - 4) - a (n - 5)) ∧
    PowerSeries.mk (fun n => (a n : ℚ)) =
      (X * (1 + 2 * X + 2 * X ^ 3)) * ((1 - X) ^ 2 * (1 + X) * (1 + X ^ 2))⁻¹ := by
  sorry

end OMA.S_oeis_a265430

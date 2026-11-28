import Mathlib

/-!
# OEIS A265428: Barker's closed form, recurrence and g.f. for the ON cells of Rule 188

Source: https://oeis.org/A265428 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry (Robert Price, Dec 08 2015), offset 0: Number of ON (black) cells in the n-th iteration of
the Rule 188 elementary cellular automaton starting with a single ON (black) cell. Data: 1, 2, 2,
4, 4, 5, 5, 7, 7, 8, 8, 10, 10, 11, 11, 13, ... The formula section states: Conjectures from
Colin Barker, Dec 09 2015 and Apr 16 2019: (Start) a(n) = (1/8)*(6*n-3*(-1)^n+(1-i)*(-i)^n+
(1+i)*i^n+9) where i = sqrt(-1). a(n) = a(n-1) + a(n-4) - a(n-5) for n > 4.
G.f.: (1+x+2*x^3-x^4) / ((1-x)^2*(1+x)*(1+x^2)). (End)

Formalization notes:
* Conventions (as in Wolfram's numbering and the entry's Mathematica program): the automaton runs
  on the integers, starting from one ON cell at position 0 on an all-OFF background, and the rule
  is applied to every cell, including the background, at each step; the new state of a cell is
  bit 4l + 2c + r of 188, where l, c, r are the old states of its left neighbor, itself and its
  right neighbor.
* a(n) is the number of ON cells among positions -n..n after n steps (the program's truncated
  row n), written as a sum over the 2n+1 cells.
* The closed form is stated in the complex numbers, with i = Complex.I, for every n >= 0 (the
  line gives no range); the recurrence in the integers; the g.f. as A(x) = N(x) * D(x)^(-1) in
  Q[[x]] (D has constant term 1).
* `main` is the conjunction of the three conjectures.
* Controls proved in the proof file: a(0..25), the entry's data.
-/

namespace OMA.S_oeis_a265428

/-- Rule 188 as a local map: the new state of a cell from (left, center, right). -/
def rule (l c r : Bool) : Bool := (188 : ℕ).testBit ((cond l 4 0) + (cond c 2 0) + (cond r 1 0))

/-- The configuration at time `t`, started from the single ON cell at 0. -/
def state : ℕ → ℤ → Bool
  | 0, i => decide (i = 0)
  | t + 1, i => rule (state t (i - 1)) (state t i) (state t (i + 1))

/-- A265428(n): the number of ON cells among `-n..n` in row `n`. -/
def a (n : ℕ) : ℕ :=
  ∑ k ∈ Finset.range (2 * n + 1), if state n ((k : ℤ) - n) then 1 else 0

open PowerSeries in
/-- Barker's conjectures: the closed form, the recurrence for n > 4, and the g.f. -/
theorem main :
    (∀ n : ℕ, (a n : ℂ) = (1 / 8) * (6 * (n : ℂ) - 3 * (-1) ^ n +
      (1 - Complex.I) * (-Complex.I) ^ n + (1 + Complex.I) * Complex.I ^ n + 9)) ∧
    (∀ n : ℕ, 4 < n → (a n : ℤ) = a (n - 1) + a (n - 4) - a (n - 5)) ∧
    PowerSeries.mk (fun n => (a n : ℚ)) =
      (1 + X + 2 * X ^ 3 - X ^ 4) * ((1 - X) ^ 2 * (1 + X) * (1 + X ^ 2))⁻¹ := by
  sorry

end OMA.S_oeis_a265428

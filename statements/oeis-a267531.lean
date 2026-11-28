import Mathlib

/-!
# OEIS A267531: Barker's and Stauduhar's conjectures for the total OFF cells of Rule 141

Source: https://oeis.org/A267531 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry (Robert Price, Jan 16 2016), offset 0: Total number of OFF (white) cells after n iterations
of the Rule 141 elementary cellular automaton starting with a single ON (black) cell. Data: 0, 2,
5, 9, 13, 18, 23, 29, 35, 42, 49, 57, 65, ... The formula section states: Conjectures from Colin
Barker, Jan 17 2016: (Start) a(n) = 2*a(n-1) - 2*a(n-3) + a(n-4) for n > 4.
G.f.: x*(2+x-x^2-x^3) / ((1-x)^3*(1+x)). (End)
Conjecture: a(n) = a(n-1) + A004526(n+5) for n > 1. - J. Stauduhar, Oct 21 2017

Formalization notes:
* Conventions (as in Wolfram's numbering and the entry's Mathematica program): the automaton runs
  on the integers, starting from one ON cell at position 0 on an all-OFF background, and the rule
  is applied to every cell, including the background, at each step; the new state of a cell is
  bit 4l + 2c + r of 141, where l, c, r are the old states of its left neighbor, itself and its
  right neighbor.
* The cells of stage t are counted where the program counts them, among positions -t..t; a(n) is
  the sum over the stages t = 0..n of the number of OFF cells there.
* A004526 is floor(m/2) (its name: Nonnegative integers repeated, floor(n/2)), written here as
  natural-number division (n + 5) / 2.
* The recurrence is stated in the integers, the g.f. as A(x) = N(x) * D(x)^(-1) in Q[[x]]
  (D has constant term 1), Stauduhar's identity in the natural numbers.
* `main` is the conjunction of the three conjectures.
* Controls proved in the proof file: a(0..21), the entry's data.
-/

namespace OMA.S_oeis_a267531

/-- Rule 141 as a local map: the new state of a cell from (left, center, right). -/
def rule (l c r : Bool) : Bool := (141 : ℕ).testBit ((cond l 4 0) + (cond c 2 0) + (cond r 1 0))

/-- The configuration at time `t`, started from the single ON cell at 0. -/
def state : ℕ → ℤ → Bool
  | 0, i => decide (i = 0)
  | t + 1, i => rule (state t (i - 1)) (state t i) (state t (i + 1))

/-- A267531(n): the number of OFF cells among `-t..t` in rows `t = 0..n`, summed. -/
def a (n : ℕ) : ℕ :=
  ∑ t ∈ Finset.range (n + 1), ∑ k ∈ Finset.range (2 * t + 1), if state t ((k : ℤ) - t) then 0 else 1

open PowerSeries in
/-- Barker's recurrence (n > 4) and g.f., and Stauduhar's identity (n > 1). -/
theorem main :
    (∀ n : ℕ, 4 < n → (a n : ℤ) = 2 * a (n - 1) - 2 * a (n - 3) + a (n - 4)) ∧
    PowerSeries.mk (fun n => (a n : ℚ)) =
      X * (2 + X - X ^ 2 - X ^ 3) * ((1 - X) ^ 3 * (1 + X))⁻¹ ∧
    (∀ n : ℕ, 1 < n → a n = a (n - 1) + (n + 5) / 2) := by
  sorry

end OMA.S_oeis_a267531

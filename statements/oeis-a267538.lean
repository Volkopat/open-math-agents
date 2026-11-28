import Mathlib

/-!
# OEIS A267538: Barker's recurrence and g.f. and Keller's floor formula for Rule 143

Source: https://oeis.org/A267538 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry (Robert Price, Jan 16 2016), offset 0: Binary representation of the middle column of the
'Rule 143' elementary cellular automaton starting with a single ON (black) cell. The formula section
states: Conjectures from Colin Barker, Jan 17 2016 and Apr 20 2019: (Start) a(n) =
11*a(n-1)-10*a(n-2) for n > 4. [n range correction by Karl V. Keller, Jr., Apr 23 2022] G.f.:
(1-x^2+x^4) / ((1-x)*(1-10*x)). (End) Conjecture: a(n) = floor(9901*10^n/9000). - Karl V. Keller,
Jr., Apr 24 2022

Formalization notes:
* Conventions (as in Wolfram's numbering and the entry's Mathematica program): the automaton runs
  on the integers, starting from one ON cell at position 0 on an all-OFF background, and the rule
  is applied to every cell, including the background, at each step; the new state of a cell is
  bit 4l + 2c + r of 143, where l, c, r are the old states of its left neighbor, itself and its
  right neighbor.
* a(n) is the states of cell 0 at times 0, 1, ..., n, read as the digits of a number in base 10
  (time 0 most significant).
* `main` is the conjunction of the three conjectures, in the entry's order. The g.f. is stated as
  A(x) = N(x) * D(x)^(-1) in Q[[x]] (D has constant term 1). The floor is natural-number division.
* Controls: the definitions give a(0..4) = 1, 11, 110, 1100, 11001, as in the entry.
-/

namespace OMA.S_oeis_a267538

/-- Rule 143 as a local map: the new state of a cell from (left, centre, right). -/
def rule (l c r : Bool) : Bool := (143 : ℕ).testBit ((cond l 4 0) + (cond c 2 0) + (cond r 1 0))

/-- The configuration at time `t`, started from the single ON cell at 0. -/
def state : ℕ → ℤ → Bool
  | 0, i => decide (i = 0)
  | t + 1, i => rule (state t (i - 1)) (state t i) (state t (i + 1))

/-- A267538(n): the middle column at times `0..n` as binary digits written in base 10. -/
def a (n : ℕ) : ℕ := ∑ t ∈ Finset.range (n + 1), if state t 0 then 10 ^ (n - t) else 0

open PowerSeries in
/-- Barker's recurrence (with Keller's range) and g.f., and Keller's floor formula. -/
theorem main :
    (∀ n : ℕ, 4 < n → (a n : ℤ) = 11 * a (n - 1) - 10 * a (n - 2)) ∧
    PowerSeries.mk (fun n => (a n : ℚ)) = (1 - X ^ 2 + X ^ 4) * ((1 - X) * (1 - 10 * X))⁻¹ ∧
    (∀ n : ℕ, a n = 9901 * 10 ^ n / 9000) := by
  sorry

end OMA.S_oeis_a267538

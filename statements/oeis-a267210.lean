import Mathlib

/-!
# OEIS A267210: Barker's recurrence and generating function for the middle column of Rule 109

Source: https://oeis.org/A267210 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry A267210 (Robert Price, Jan 11 2016), offset 0: Decimal representation of the middle column of
the Rule 109 elementary cellular automaton starting with a single ON (black) cell.
Formula section:
Conjectures from Colin Barker, Jan 13 2016 and Apr 19 2019:
a(n) = 2*a(n-1)+a(n-3)-2*a(n-4) for n>3.
G.f.: (1+x+x^2-x^3) / ((1-x)*(1-2*x)*(1+x+x^2)).

Formalization notes:
* Rule numbering: Wolfram's numbering of elementary cellular automata; the new value of cell x is
  bit 4l + 2c + r of the rule number, where l, c, r are the old values of cells x-1, x, x+1.
* Initial condition: at stage 0 cell 0 is ON and every other cell of Z is OFF; each stage applies
  the rule to every cell, so the background evolves with the rule (Rule 109 maps 000 to ON), as
  CellularAutomaton[rule, {{1},0}, ...] does in the entry's program.
* Reading convention: a(n) reads the middle cells (cell 0) of stages 0..n as a binary number, stage
  0 most significant, as the entry's program does (keep the middle cell of each row, FromDigits base
  2).
* The statement is the conjunction of the 2 conjectures of the site's problem, in the entry's order.
  The recurrence is stated in the integers. The generating function is A(x) = Sum_{n >= 0} a(n) x^n
  in the formal power series ring over the rationals, and the identity is A = N * D⁻¹, where D has a
  nonzero constant term.
* Controls proved in the proof file (theorem controls): the definition gives a(n) for n = 0..68; the
  first 33 of these values are all the entry's listed terms, 1, 3, 7, 14, 29, 59, 118, 237, 475,
  950, 1901, 3803, ....
-/

namespace OMA.S_oeis_a267210

open PowerSeries

/-- One step of an elementary cellular automaton in Wolfram's numbering. -/
def step (rule : ℕ) (s : ℤ → Bool) (x : ℤ) : Bool :=
  Nat.testBit rule (4 * (s (x - 1)).toNat + 2 * (s x).toNat + (s (x + 1)).toNat)

/-- The automaton started from a single ON cell at 0. -/
def state (rule : ℕ) : ℕ → ℤ → Bool
  | 0 => fun x => decide (x = 0)
  | n + 1 => step rule (state rule n)

/-- The middle cell of stage n of Rule 109. -/
def c (n : ℕ) : ℕ := (state 109 n 0).toNat

/-- A267210(n): the middle cells of stages 0..n read as a binary number, stage 0 most significant. -/
def a (n : ℕ) : ℕ := ∑ k ∈ Finset.range (n + 1), c k * 2 ^ (n - k)

/-- The generating function Sum_{n >= 0} a(n) x^n. -/
noncomputable def A : ℚ⟦X⟧ := PowerSeries.mk fun n => (a n : ℚ)

/-- Barker's recurrence and generating function. -/
theorem main :
    (∀ n : ℕ, 3 < n → (a n : ℤ) = 2 * a (n - 1) + a (n - 3) - 2 * a (n - 4)) ∧
    A = (1 + X + X ^ 2 - X ^ 3) * ((1 - X) * (1 - 2 * X) * (1 + X + X ^ 2))⁻¹ := by
  sorry

end OMA.S_oeis_a267210

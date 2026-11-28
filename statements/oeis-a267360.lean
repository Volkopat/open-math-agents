import Mathlib

/-!
# OEIS A267360: Barker's recurrence and generating function for the decimal rows of Rule 125

Source: https://oeis.org/A267360 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry A267360 (Robert Price, Jan 13 2016), offset 0: Decimal representation of the n-th iteration of
the Rule 125 elementary cellular automaton starting with a single ON (black) cell.
Formula section:
Conjectures from Colin Barker, Jan 14 2016 and Apr 19 2019:
a(n) = 17*a(n-2)-16*a(n-4) for n>8.
G.f.: (1+3*x+11*x^2-4*x^3+36*x^4-176*x^5+16*x^6+192*x^7-64*x^8) / ((1-x)*(1+x)*(1-4*x)*(1+4*x)).

Formalization notes:
* Rule numbering: Wolfram's numbering of elementary cellular automata; the new value of cell x is
  bit 4l + 2c + r of the rule number, where l, c, r are the old values of cells x-1, x, x+1.
* Initial condition: at stage 0 cell 0 is ON and every other cell of Z is OFF; each stage applies
  the rule to every cell, so the background evolves with the rule (Rule 125 maps 000 to ON), as
  CellularAutomaton[rule, {{1},0}, ...] does in the entry's program.
* Reading convention: a(n) reads the cells -n..n of stage n as a binary number with the leftmost
  cell most significant, as the entry's program does (Take the middle 2n+1 cells, FromDigits base
  2).
* The statement is the conjunction of the 2 conjectures of the site's problem, in the entry's order.
  The recurrence is stated in the integers. The generating function is A(x) = Sum_{n >= 0} a(n) x^n
  in the formal power series ring over the rationals, and the identity is A = N * D⁻¹, where D has a
  nonzero constant term.
* Controls proved in the proof file (theorem controls): the definition gives a(n) for n = 0..27; the
  first 26 of these values are all the entry's listed terms, 1, 3, 28, 47, 496, 575, 8000, 9215,
  128000, 147455, 2048000, 2359295, ....
-/

namespace OMA.S_oeis_a267360

open PowerSeries

/-- One step of an elementary cellular automaton in Wolfram's numbering. -/
def step (rule : ℕ) (s : ℤ → Bool) (x : ℤ) : Bool :=
  Nat.testBit rule (4 * (s (x - 1)).toNat + 2 * (s x).toNat + (s (x + 1)).toNat)

/-- The automaton started from a single ON cell at 0. -/
def state (rule : ℕ) : ℕ → ℤ → Bool
  | 0 => fun x => decide (x = 0)
  | n + 1 => step rule (state rule n)

/-- Row n (cells -n..n) read as a binary number, leftmost cell most significant. -/
def rowValue (s : ℤ → Bool) (n : ℕ) : ℕ :=
  ∑ i ∈ Finset.range (2 * n + 1), (s ((n : ℤ) - i)).toNat * 2 ^ i

/-- A267360(n). -/
def a (n : ℕ) : ℕ := rowValue (state 125 n) n

/-- The generating function Sum_{n >= 0} a(n) x^n. -/
noncomputable def A : ℚ⟦X⟧ := PowerSeries.mk fun n => (a n : ℚ)

/-- Barker's recurrence and generating function. -/
theorem main :
    (∀ n : ℕ, 8 < n → (a n : ℤ) = 17 * a (n - 2) - 16 * a (n - 4)) ∧
    A = (1 + 3 * X + 11 * X ^ 2 - 4 * X ^ 3 + 36 * X ^ 4 - 176 * X ^ 5 + 16 * X ^ 6 + 192 * X ^ 7 - 64 * X ^ 8) *
      ((1 - X) * (1 + X) * (1 - 4 * X) * (1 + 4 * X))⁻¹ := by
  sorry

end OMA.S_oeis_a267360

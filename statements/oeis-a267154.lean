import Mathlib

/-!
# OEIS A267154: Barker's recurrence and generating function for the decimal rows of Rule 107

Source: https://oeis.org/A267154 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry A267154 (Robert Price, Jan 11 2016), offset 0: Decimal representation of the n-th iteration of
the Rule 107 elementary cellular automaton starting with a single ON (black) cell.
Formula section:
Conjectures from Colin Barker, Jan 11 2016 and Apr 19 2019:
a(n) = 16*a(n-2)+a(n-4)-16*a(n-6) for n>12.
G.f.: (1+4*x-5*x^2+46*x^3-58*x^4+214*x^5-1424*x^6+816*x^7-5744*x^8 +2624*x^9 -20416*x^10 +19456*x^11
-103424*x^12) / ((1-x)*(1+x)*(1-4*x)*(1+4*x)*(1+x^2)).

Formalization notes:
* Rule numbering: Wolfram's numbering of elementary cellular automata; the new value of cell x is
  bit 4l + 2c + r of the rule number, where l, c, r are the old values of cells x-1, x, x+1.
* Initial condition: at stage 0 cell 0 is ON and every other cell of Z is OFF; each stage applies
  the rule to every cell, so the background evolves with the rule (Rule 107 maps 000 to ON), as
  CellularAutomaton[rule, {{1},0}, ...] does in the entry's program.
* Reading convention: a(n) reads the cells -n..n of stage n as a binary number with the leftmost
  cell most significant, as the entry's program does (Take the middle 2n+1 cells, FromDigits base
  2).
* The statement is the conjunction of the 2 conjectures of the site's problem, in the entry's order.
  The recurrence is stated in the integers. The generating function is A(x) = Sum_{n >= 0} a(n) x^n
  in the formal power series ring over the rationals, and the identity is A = N * D⁻¹, where D has a
  nonzero constant term.
* Controls proved in the proof file (theorem controls): the definition gives a(n) for n = 0..39; the
  first 30 of these values are all the entry's listed terms, 1, 4, 11, 110, 119, 1978, 475, 32510,
  1799, 523002, 6939, 8388350, ....
-/

namespace OMA.S_oeis_a267154

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

/-- A267154(n). -/
def a (n : ℕ) : ℕ := rowValue (state 107 n) n

/-- The generating function Sum_{n >= 0} a(n) x^n. -/
noncomputable def A : ℚ⟦X⟧ := PowerSeries.mk fun n => (a n : ℚ)

/-- Barker's recurrence and generating function. -/
theorem main :
    (∀ n : ℕ, 12 < n → (a n : ℤ) = 16 * a (n - 2) + a (n - 4) - 16 * a (n - 6)) ∧
    A = (1 + 4 * X - 5 * X ^ 2 + 46 * X ^ 3 - 58 * X ^ 4 + 214 * X ^ 5 - 1424 * X ^ 6 + 816 * X ^ 7 - 5744 * X ^ 8 + 2624 * X ^ 9 - 20416 * X ^ 10 + 19456 * X ^ 11 - 103424 * X ^ 12) *
      ((1 - X) * (1 + X) * (1 - 4 * X) * (1 + 4 * X) * (1 + X ^ 2))⁻¹ := by
  sorry

end OMA.S_oeis_a267154

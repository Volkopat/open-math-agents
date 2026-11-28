import Mathlib

/-!
# OEIS A267052: Barker's closed form, recurrence and g.f. for the decimal rows of Rule 92

Source: https://oeis.org/A267052 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry A267052 (Robert Price, Jan 09 2016), offset 0: Decimal representation of the n-th iteration of
the Rule 92 elementary cellular automaton starting with a single ON (black) cell.
Formula section:
Conjectures from Colin Barker, Jan 10 2016 and Apr 17 2019:
a(n) = (3+2*(-1)^n+2^(2+n))/3 for n>0.
a(n) = 2*a(n-1)+a(n-2)-2*a(n-3) for n>3.
G.f.: (1+x-4*x^3) / ((1-x)*(1+x)*(1-2*x)).

Formalization notes:
* Rule numbering: Wolfram's numbering of elementary cellular automata; the new value of cell x is
  bit 4l + 2c + r of the rule number, where l, c, r are the old values of cells x-1, x, x+1.
* Initial condition: at stage 0 cell 0 is ON and every other cell of Z is OFF; each stage applies
  the rule to every cell, so the background evolves with the rule (Rule 92 maps 000 to OFF, so it
  stays OFF), as CellularAutomaton[rule, {{1},0}, ...] does in the entry's program.
* Reading convention: a(n) reads the cells -n..n of stage n as a binary number with the leftmost
  cell most significant, as the entry's program does (Take the middle 2n+1 cells, FromDigits base
  2).
* The statement is the conjunction of the 3 conjectures of the site's problem, in the entry's order.
  The recurrence is stated in the integers. The closed form is stated in the rationals, where every
  division is exact. The generating function is A(x) = Sum_{n >= 0} a(n) x^n in the formal power
  series ring over the rationals, and the identity is A = N * D⁻¹, where D has a nonzero constant
  term.
* Controls proved in the proof file (theorem controls): the definition gives a(n) for n = 0..16
  equal to the entry's first 17 terms, 1, 3, 7, 11, 23, 43, 87, 171, 343, 683, 1367, 2731, ....
-/

namespace OMA.S_oeis_a267052

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

/-- A267052(n). -/
def a (n : ℕ) : ℕ := rowValue (state 92 n) n

/-- The generating function Sum_{n >= 0} a(n) x^n. -/
noncomputable def A : ℚ⟦X⟧ := PowerSeries.mk fun n => (a n : ℚ)

/-- Barker's closed form, recurrence and generating function. -/
theorem main :
    (∀ n : ℕ, 0 < n → (a n : ℚ) = (3 + 2 * (-1) ^ n + 2 ^ (2 + n)) / 3) ∧
    (∀ n : ℕ, 3 < n → (a n : ℤ) = 2 * a (n - 1) + a (n - 2) - 2 * a (n - 3)) ∧
    A = (1 + X - 4 * X ^ 3) * ((1 - X) * (1 + X) * (1 - 2 * X))⁻¹ := by
  sorry

end OMA.S_oeis_a267052

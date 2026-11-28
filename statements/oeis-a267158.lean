import Mathlib

/-!
# OEIS A267158: Barker's recurrence and generating function for the ON cells of Rule 107

Source: https://oeis.org/A267158 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry A267158 (Robert Price, Jan 11 2016), offset 0: Number of ON (black) cells in the n-th
iteration of the Rule 107 elementary cellular automaton starting with a single ON (black) cell.
Formula section:
Conjectures from Colin Barker, Jan 11 2016 and Apr 19 2019:
a(n) = a(n-2)+a(n-4)-a(n-6) for n>12.
G.f.: (1+x+2*x^2+4*x^3+2*x^4+2*x^5-x^6+x^7-4*x^8-x^9+x^10+x^11-x^12) / ((1-x)^2*(1+x)^2*(1+x^2)).

Formalization notes:
* Rule numbering: Wolfram's numbering of elementary cellular automata; the new value of cell x is
  bit 4l + 2c + r of the rule number, where l, c, r are the old values of cells x-1, x, x+1.
* Initial condition: at stage 0 cell 0 is ON and every other cell of Z is OFF; each stage applies
  the rule to every cell, so the background evolves with the rule (Rule 107 maps 000 to ON), as
  CellularAutomaton[rule, {{1},0}, ...] does in the entry's program.
* Counting convention: a(n) is the number of ON cells among the cells -n..n of stage n, as the
  entry's program does (Take the middle 2n+1 cells, Total).
* The statement is the conjunction of the 2 conjectures of the site's problem, in the entry's order.
  The recurrence is stated in the integers. The generating function is A(x) = Sum_{n >= 0} a(n) x^n
  in the formal power series ring over the rationals, and the identity is A = N * D⁻¹, where D has a
  nonzero constant term.
* Controls proved in the proof file (theorem controls): the definition gives a(n) for n = 0..39
  equal to the entry's first 40 terms, 1, 1, 3, 5, 6, 8, 7, 13, 6, 15, 8, 21, ....
-/

namespace OMA.S_oeis_a267158

open PowerSeries

/-- One step of an elementary cellular automaton in Wolfram's numbering. -/
def step (rule : ℕ) (s : ℤ → Bool) (x : ℤ) : Bool :=
  Nat.testBit rule (4 * (s (x - 1)).toNat + 2 * (s x).toNat + (s (x + 1)).toNat)

/-- The automaton started from a single ON cell at 0. -/
def state (rule : ℕ) : ℕ → ℤ → Bool
  | 0 => fun x => decide (x = 0)
  | n + 1 => step rule (state rule n)

/-- The number of ON cells of row n among the cells -n..n. -/
def onCount (s : ℤ → Bool) (n : ℕ) : ℕ :=
  ∑ i ∈ Finset.range (2 * n + 1), (s ((n : ℤ) - i)).toNat

/-- A267158(n). -/
def a (n : ℕ) : ℕ := onCount (state 107 n) n

/-- The generating function Sum_{n >= 0} a(n) x^n. -/
noncomputable def A : ℚ⟦X⟧ := PowerSeries.mk fun n => (a n : ℚ)

/-- Barker's recurrence and generating function. -/
theorem main :
    (∀ n : ℕ, 12 < n → (a n : ℤ) = a (n - 2) + a (n - 4) - a (n - 6)) ∧
    A = (1 + X + 2 * X ^ 2 + 4 * X ^ 3 + 2 * X ^ 4 + 2 * X ^ 5 - X ^ 6 + X ^ 7 - 4 * X ^ 8 - X ^ 9 + X ^ 10 + X ^ 11 - X ^ 12) *
      ((1 - X) ^ 2 * (1 + X) ^ 2 * (1 + X ^ 2))⁻¹ := by
  sorry

end OMA.S_oeis_a267158

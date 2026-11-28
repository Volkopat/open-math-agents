import Mathlib

/-!
# OEIS A266718: Barker's recurrence and generating function for Rule 59

Source: https://oeis.org/A266718 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry A266718 (Robert Price, Jan 03 2016), offset 0: Decimal representation of the n-th iteration
of the Rule 59 elementary cellular automaton starting with a single ON (black) cell.
Formula section:
Conjectures from Colin Barker, Jan 04 2016 and Apr 18 2019:
a(n) = 19*a(n-2)-50*a(n-4)+32*a(n-6) for n>6.
G.f.: (1-2*x)*(1+7*x+x^2+30*x^3+8*x^4-32*x^5) / ((1-x)*(1+x)*(1-4*x)*(1+4*x)*(1-2*x^2)).

Formalization notes:
* Rule numbering: Wolfram's numbering of elementary cellular automata; the new value of cell x is
  bit 4l + 2c + r of the rule number, where l, c, r are the old values of cells x-1, x, x+1.
* Initial condition: at stage 0 cell 0 is ON and every other cell of Z is OFF; each stage applies
  the rule to every cell, so the background evolves with the rule (Rule 59 maps 000 to ON), as
  CellularAutomaton[rule, {{1},0}, ...] does in the entry's program.
* Reading convention: a(n) reads the cells -n..n of stage n as a binary number with the leftmost
  cell most significant, as the entry's program does (Take the middle 2n+1 cells, FromDigits base
  2).
* The statement is the conjunction of both conjectures. The recurrence is stated in the integers.
  The generating function is A(x) = Sum_{n >= 0} a(n) x^n in the formal power series ring over
  the rationals, and the identity is A = N * D⁻¹, where D has constant term 1.
* Controls proved in the proof file: the definition gives 1, 5, 6, 123, 12, 2039, 24, 32751, 48,
  524255, 96, 8388543, 192, 134217599, 384 for n = 0..14, the entry's first terms.
-/

namespace OMA.S_oeis_a266718

open PowerSeries

/-- One step of an elementary cellular automaton in Wolfram's numbering: the new value of cell `x`
is bit `4l + 2c + r` of `rule`, where `l, c, r` are the old values of cells `x-1, x, x+1`. -/
def step (rule : ℕ) (s : ℤ → Bool) (x : ℤ) : Bool :=
  Nat.testBit rule (4 * (s (x - 1)).toNat + 2 * (s x).toNat + (s (x + 1)).toNat)

/-- The automaton started from a single ON cell at `0`. -/
def state (rule : ℕ) : ℕ → ℤ → Bool
  | 0 => fun x => decide (x = 0)
  | n + 1 => step rule (state rule n)

/-- Row `n` (cells `-n..n`) read as a binary number, leftmost cell most significant. -/
def rowValue (s : ℤ → Bool) (n : ℕ) : ℕ :=
  ∑ i ∈ Finset.range (2 * n + 1), (s ((n : ℤ) - i)).toNat * 2 ^ i

/-- A266718(n). -/
def a (n : ℕ) : ℕ := rowValue (state 59 n) n

/-- The generating function `Sum a(n) x^n`. -/
noncomputable def A : ℚ⟦X⟧ := PowerSeries.mk fun n => (a n : ℚ)

/-- Barker's recurrence and generating function. -/
theorem main :
    (∀ n : ℕ, 6 < n → (a n : ℤ) = 19 * a (n - 2) - 50 * a (n - 4) + 32 * a (n - 6)) ∧
    A = (1 - 2 * X) * (1 + 7 * X + X ^ 2 + 30 * X ^ 3 + 8 * X ^ 4 - 32 * X ^ 5) *
      ((1 - X) * (1 + X) * (1 - 4 * X) * (1 + 4 * X) * (1 - 2 * X ^ 2))⁻¹ := by
  sorry

end OMA.S_oeis_a266718

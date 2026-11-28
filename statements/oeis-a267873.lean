import Mathlib

/-!
# A267873: Number of ON (black) cells in the n-th iteration of the "Rule 235" elementary cellular automaton starting with a single ON (black) cell

Source: https://oeis.org/A267873 (OEIS Foundation, CC BY-SA 4.0).
Credit: @Mapika (AI-assisted: Claude Code, model claude-opus-5-5).

Entry A267873 (Robert Price, Jan 21 2016), offset 0. Formula section, verbatim:
Conjectures from Colin Barker, Jan 22 2016 and Apr 20 2019:
a(n) = 2*a(n-1)-a(n-2) for n>2.
G.f.: (1-x+3*x^2-x^4) / (1-x)^2.

Formalization notes:
* Rule numbering: Wolfram's numbering of elementary cellular automata; the new value of cell x is
  bit 4l + 2c + r of the rule number, where l, c, r are the old values of cells x-1, x, x+1.
* Initial condition: at stage 0 cell 0 is ON and every other cell of Z is OFF; each stage applies
  the rule to every cell, so the background evolves with the rule (Rule 235 maps 000 to ON).
* Counting convention: a(n) is the number of ON cells among the cells -n..n of stage n (the
  middle 2n+1 cells, as in the entry's program).
* The statement is the conjunction of the two conjectures, on the range the entry gives
  (n > 2 for the recurrence). The recurrence is stated in the integers. The generating function
  is A(x) = Sum_{n >= 0} a(n) x^n in the formal power series ring over the rationals, and the
  identity is A = N * D⁻¹, where D = (1-x)^2 has constant term 1.
* Controls from the entry: the definition gives 1, 1, 4, 7, 9, 11, 13, 15, 17 for n = 0..8,
  matching the entry's data.
* Remark: since a(2), a(3), a(4) = 4, 7, 9 and 2*7 - 4 = 10, the recurrence as printed fails at
  n = 4 (the g.f., whose numerator has degree 4, gives it only for n > 4). The statement keeps the
  range the entry prints.
-/

namespace OMA.S_oeis_a267873

open PowerSeries

/-- One step of an elementary cellular automaton in Wolfram's numbering. -/
def step (rule : ℕ) (s : ℤ → Bool) (x : ℤ) : Bool :=
  Nat.testBit rule (4 * (s (x - 1)).toNat + 2 * (s x).toNat + (s (x + 1)).toNat)

/-- The automaton started from a single ON cell at 0. -/
def state (rule : ℕ) : ℕ → ℤ → Bool
  | 0 => fun x => decide (x = 0)
  | n + 1 => step rule (state rule n)

/-- The number of ON cells among the cells -n..n of a row. -/
def onCount (s : ℤ → Bool) (n : ℕ) : ℕ :=
  ∑ i ∈ Finset.range (2 * n + 1), (s ((n : ℤ) - i)).toNat

/-- A267873(n). -/
def a (n : ℕ) : ℕ := onCount (state 235 n) n

/-- The generating function Sum_{n >= 0} a(n) x^n. -/
noncomputable def A : ℚ⟦X⟧ := PowerSeries.mk fun n => (a n : ℚ)

/-- Barker's recurrence and generating function for OEIS A267873. -/
theorem main :
    (∀ n : ℕ, 2 < n → (a n : ℤ) = 2 * a (n - 1) - a (n - 2)) ∧
    A = (1 - X + 3 * X ^ 2 - X ^ 4) * ((1 - X) ^ 2)⁻¹ := by
  sorry

end OMA.S_oeis_a267873

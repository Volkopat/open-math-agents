import Mathlib

/-!
# OEIS A267524: Barker's recurrence and generating function for the middle column of Rule 139

Source: https://oeis.org/A267524 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry A267524 (Robert Price, Jan 16 2016), offset 0: Binary representation of the middle column of
the Rule 139 elementary cellular automaton starting with a single ON (black) cell.
Formula section:
Conjectures from Colin Barker, Jan 16 2016 and Apr 19 2019:
a(n) = 11*a(n-1) - 10*a(n-2) for n > 3. [n range correction - Karl V. Keller, Jr., Apr 08 2022]
G.f.: (1-x+x^3) / ((1-x)*(1-10*x)).

Formalization notes:
* Rule numbering: Wolfram's numbering of elementary cellular automata; the new value of cell x is
  bit 4l + 2c + r of the rule number, where l, c, r are the old values of cells x-1, x, x+1.
* Initial condition: at stage 0 cell 0 is ON and every other cell of Z is OFF; each stage applies
  the rule to every cell, so the background evolves with the rule (Rule 139 maps 000 to ON), as
  CellularAutomaton[rule, {{1},0}, ...] does in the entry's program.
* Reading convention: a(n) writes the middle cells (cell 0) of stages 0..n as binary digits, stage 0
  first, and reads them as a decimal number, as the entry's program does (keep the middle cell of
  each row, FromDigits in base 10).
* The statement is the conjunction of the 2 conjectures of the site's problem, in the entry's order.
  The recurrence is stated in the integers. The generating function is A(x) = Sum_{n >= 0} a(n) x^n
  in the formal power series ring over the rationals, and the identity is A = N * D⁻¹, where D has a
  nonzero constant term.
* Controls proved in the proof file (theorem controls): the definition gives a(n) for n = 0..16
  equal to the entry's first 17 terms, 1, 10, 100, 1001, 10011, 100111, 1001111, 10011111,
  100111111, 1001111111, 10011111111, 100111111111, ....
-/

namespace OMA.S_oeis_a267524

open PowerSeries

/-- One step of an elementary cellular automaton in Wolfram's numbering. -/
def step (rule : ℕ) (s : ℤ → Bool) (x : ℤ) : Bool :=
  Nat.testBit rule (4 * (s (x - 1)).toNat + 2 * (s x).toNat + (s (x + 1)).toNat)

/-- The automaton started from a single ON cell at 0. -/
def state (rule : ℕ) : ℕ → ℤ → Bool
  | 0 => fun x => decide (x = 0)
  | n + 1 => step rule (state rule n)

/-- The middle cell of stage n of Rule 139. -/
def c (n : ℕ) : ℕ := (state 139 n 0).toNat

/-- A267524(n): the middle cells of stages 0..n as binary digits, stage 0 first, read in base 10. -/
def a (n : ℕ) : ℕ := ∑ k ∈ Finset.range (n + 1), c k * 10 ^ (n - k)

/-- The generating function Sum_{n >= 0} a(n) x^n. -/
noncomputable def A : ℚ⟦X⟧ := PowerSeries.mk fun n => (a n : ℚ)

/-- Barker's recurrence and generating function. -/
theorem main :
    (∀ n : ℕ, 3 < n → (a n : ℤ) = 11 * a (n - 1) - 10 * a (n - 2)) ∧
    A = (1 - X + X ^ 3) * ((1 - X) * (1 - 10 * X))⁻¹ := by
  sorry

end OMA.S_oeis_a267524

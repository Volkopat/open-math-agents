import Mathlib

/-!
# A266680: Binary representation of the middle column of the "Rule 175" elementary cellular automaton starting with a single ON (black) cell.

Source: https://oeis.org/A266680 (OEIS Foundation, CC BY-SA 4.0).
Credit: @Mapika (AI-assisted: Claude Code, model claude-opus-5-5).

Entry A266680 (Robert Price, Jan 18 2016), offset 0. Formula section, verbatim:
Conjectures from Colin Barker, Jan 19 2016 and Apr 18 2019:
a(n) = 11*a(n-1) - 10*a(n-2) for n > 3.
G.f.: (1-x^2+x^3) / ((1-x)*(1-10*x)).

Formalization notes:
* Rule numbering: Wolfram's numbering of elementary cellular automata; the new value of cell x is
  bit 4l + 2c + r of the rule number, where l, c, r are the old values of cells x-1, x, x+1.
* Initial condition: at stage 0 cell 0 is ON and every other cell of Z is OFF; each stage applies
  the rule to every cell, so the background evolves with the rule (Rule 175 maps 000 to ON).
* Counting convention: a(n) writes the middle cells (cell 0) of stages 0..n as binary digits,
  stage 0 first (most significant), and reads them in base 10, as the entry's data shows
  (1, 11, 110, 1101, ...).
* The statement is the conjunction of the two conjectures, on the range the entry gives
  (n > 3 for the recurrence). The recurrence is stated in the integers. The generating function
  is A(x) = Sum_{n >= 0} a(n) x^n in the formal power series ring over the rationals, and the
  identity is A = N * D⁻¹, where D has constant term 1.
* Controls from the entry: the definition gives 1, 11, 110, 1101, 11011, 110111, 1101111 for
  n = 0..6, matching the entry's data.
-/

namespace OMA.S_oeis_a266680

open PowerSeries

/-- One step of an elementary cellular automaton in Wolfram's numbering. -/
def step (rule : ℕ) (s : ℤ → Bool) (x : ℤ) : Bool :=
  Nat.testBit rule (4 * (s (x - 1)).toNat + 2 * (s x).toNat + (s (x + 1)).toNat)

/-- The automaton started from a single ON cell at 0. -/
def state (rule : ℕ) : ℕ → ℤ → Bool
  | 0 => fun x => decide (x = 0)
  | n + 1 => step rule (state rule n)

/-- The middle cell of stage n of Rule 175. -/
def c (n : ℕ) : ℕ := (state 175 n 0).toNat

/-- A266680(n): the middle cells of stages 0..n as binary digits, stage 0 first, read in base 10. -/
def a (n : ℕ) : ℕ := ∑ k ∈ Finset.range (n + 1), c k * 10 ^ (n - k)

/-- The generating function Sum_{n >= 0} a(n) x^n. -/
noncomputable def A : ℚ⟦X⟧ := PowerSeries.mk fun n => (a n : ℚ)

/-- Barker's recurrence and generating function for OEIS A266680. -/
theorem main :
    (∀ n : ℕ, 3 < n → (a n : ℤ) = 11 * a (n - 1) - 10 * a (n - 2)) ∧
    A = (1 - X ^ 2 + X ^ 3) * ((1 - X) * (1 - 10 * X))⁻¹ := by
  sorry

end OMA.S_oeis_a266680

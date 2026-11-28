import Mathlib

/-!
# OEIS A267293: Barker's recurrence and generating function for the binary rows of Rule 121

Source: https://oeis.org/A267293 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry A267293 (Robert Price, Jan 12 2016), offset 0: Binary representation of the n-th iteration of
the Rule 121 elementary cellular automaton starting with a single ON (black) cell.
Formula section:
Conjectures from Colin Barker, Jan 15 2016 and Apr 19 2019:
a(n) = a(n-2)+100000000*a(n-4)-100000000*a(n-6) for n>12.
G.f.: (1 +x +11009*x^2 +111010*x^3 +11000090*x^4 +910990100*x^5 +90098900*x^6 +9099010000*x^7
-1109990110000*x^8 +979901000000*x^9 -108789011000000*x^10 -989900000000*x^11 +109898900000000*x^12)
/ ((1 -x)*(1 +x)*(1 -100*x)*(1 +100*x)*(1 +10000*x^2)).

Formalization notes:
* Rule numbering: Wolfram's numbering of elementary cellular automata; the new value of cell x is
  bit 4l + 2c + r of the rule number, where l, c, r are the old values of cells x-1, x, x+1.
* Initial condition: at stage 0 cell 0 is ON and every other cell of Z is OFF; each stage applies
  the rule to every cell, so the background evolves with the rule (Rule 121 maps 000 to ON), as
  CellularAutomaton[rule, {{1},0}, ...] does in the entry's program.
* Reading convention: a(n) writes the cells -n..n of stage n as a string of binary digits, leftmost
  cell first, and reads the string as a decimal number (leading OFF cells contribute leading zeros),
  as the entry's program does (Take the middle 2n+1 cells, FromDigits in base 10).
* The statement is the conjunction of the 2 conjectures of the site's problem, in the entry's order.
  The recurrence is stated in the integers. The generating function is A(x) = Sum_{n >= 0} a(n) x^n
  in the formal power series ring over the rationals, and the identity is A = N * D⁻¹, where D has a
  nonzero constant term.
* Controls proved in the proof file (theorem controls): the definition gives a(n) for n = 0..39; the
  first 15 of these values are all the entry's listed terms, 1, 1, 11010, 111011, 111011100,
  1011101111, 1101101110000, 11111110111111, 11100000111000000, 101111101011111111,
  110110001101100000000, 1111111011111111111111, ....
-/

namespace OMA.S_oeis_a267293

open PowerSeries

/-- One step of an elementary cellular automaton in Wolfram's numbering. -/
def step (rule : ℕ) (s : ℤ → Bool) (x : ℤ) : Bool :=
  Nat.testBit rule (4 * (s (x - 1)).toNat + 2 * (s x).toNat + (s (x + 1)).toNat)

/-- The automaton started from a single ON cell at 0. -/
def state (rule : ℕ) : ℕ → ℤ → Bool
  | 0 => fun x => decide (x = 0)
  | n + 1 => step rule (state rule n)

/-- Row `n` (cells `-n..n`) written as binary digits, leftmost cell first, read in base 10. -/
def rowDigits (s : ℤ → Bool) (n : ℕ) : ℕ :=
  ∑ i ∈ Finset.range (2 * n + 1), (s ((n : ℤ) - i)).toNat * 10 ^ i

/-- A267293(n). -/
def a (n : ℕ) : ℕ := rowDigits (state 121 n) n

/-- The generating function Sum_{n >= 0} a(n) x^n. -/
noncomputable def A : ℚ⟦X⟧ := PowerSeries.mk fun n => (a n : ℚ)

/-- Barker's recurrence and generating function. -/
theorem main :
    (∀ n : ℕ, 12 < n → (a n : ℤ) = a (n - 2) + 100000000 * a (n - 4) - 100000000 * a (n - 6)) ∧
    A = (1 + X + 11009 * X ^ 2 + 111010 * X ^ 3 + 11000090 * X ^ 4 + 910990100 * X ^ 5 + 90098900 * X ^ 6 + 9099010000 * X ^ 7 - 1109990110000 * X ^ 8 + 979901000000 * X ^ 9 - 108789011000000 * X ^ 10 - 989900000000 * X ^ 11 + 109898900000000 * X ^ 12) *
      ((1 - X) * (1 + X) * (1 - 100 * X) * (1 + 100 * X) * (1 + 10000 * X ^ 2))⁻¹ := by
  sorry

end OMA.S_oeis_a267293

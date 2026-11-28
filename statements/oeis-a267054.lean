import Mathlib

/-!
# OEIS A267054: Barker's recurrence and generating function for the binary rows of Rule 93

Source: https://oeis.org/A267054 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry A267054 (Robert Price, Jan 09 2016), offset 0: Binary representation of the n-th iteration of
the Rule 93 elementary cellular automaton starting with a single ON (black) cell.
Formula section:
Conjectures from Colin Barker, Jan 10 2016 and Apr 19 2019:
a(n) = 10101*a(n-2)-1010100*a(n-4)+1000000*a(n-6) for n>5.
G.f.: (1+11*x-x^2-10000*x^3-100000*x^5) / ((1-x)*(1+x)*(1-10*x)*(1+10*x)*(1-100*x)*(1+100*x)).

Formalization notes:
* Rule numbering: Wolfram's numbering of elementary cellular automata; the new value of cell x is
  bit 4l + 2c + r of the rule number, where l, c, r are the old values of cells x-1, x, x+1.
* Initial condition: at stage 0 cell 0 is ON and every other cell of Z is OFF; each stage applies
  the rule to every cell, so the background evolves with the rule (Rule 93 maps 000 to ON), as
  CellularAutomaton[rule, {{1},0}, ...] does in the entry's program.
* Reading convention: a(n) writes the cells -n..n of stage n as a string of binary digits, leftmost
  cell first, and reads the string as a decimal number (leading OFF cells contribute leading zeros),
  as the entry's program does (Take the middle 2n+1 cells, FromDigits in base 10).
* The statement is the conjunction of the 2 conjectures of the site's problem, in the entry's order.
  The recurrence is stated in the integers. The generating function is A(x) = Sum_{n >= 0} a(n) x^n
  in the formal power series ring over the rationals, and the identity is A = N * D⁻¹, where D has a
  nonzero constant term.
* Controls proved in the proof file (theorem controls): the definition gives a(n) for n = 0..21; the
  first 15 of these values are all the entry's listed terms, 1, 11, 10100, 101111, 101010000,
  1010111111, 1010101000000, 10101011111111, 10101010100000000, 101010101111111111,
  101010101010000000000, 1010101010111111111111, ....
-/

namespace OMA.S_oeis_a267054

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

/-- A267054(n). -/
def a (n : ℕ) : ℕ := rowDigits (state 93 n) n

/-- The generating function Sum_{n >= 0} a(n) x^n. -/
noncomputable def A : ℚ⟦X⟧ := PowerSeries.mk fun n => (a n : ℚ)

/-- Barker's recurrence and generating function. -/
theorem main :
    (∀ n : ℕ, 5 < n → (a n : ℤ) = 10101 * a (n - 2) - 1010100 * a (n - 4) + 1000000 * a (n - 6)) ∧
    A = (1 + 11 * X - X ^ 2 - 10000 * X ^ 3 - 100000 * X ^ 5) *
      ((1 - X) * (1 + X) * (1 - 10 * X) * (1 + 10 * X) * (1 - 100 * X) * (1 + 100 * X))⁻¹ := by
  sorry

end OMA.S_oeis_a267054

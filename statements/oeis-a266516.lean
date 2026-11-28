import Mathlib

/-!
# OEIS A266516: Keller's closed forms for the decimal rows of Rule 29

Source: https://oeis.org/A266516 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry A266516 (Robert Price, Dec 30 2015), offset 0: Decimal representation of the n-th iteration of
the Rule 29 elementary cellular automaton starting with a single ON (black) cell.
Formula section:
Conjecture: a(n) = 2*(4^n - 2^n) - 1 for odd n; a(n) = 2^n for even n. - Karl V. Keller, Jr.,
Oct 03 2021

Formalization notes:
* Rule numbering: Wolfram's numbering of elementary cellular automata; the new value of cell x is
  bit 4l + 2c + r of the rule number, where l, c, r are the old values of cells x-1, x, x+1.
* Initial condition: at stage 0 cell 0 is ON and every other cell of Z is OFF; each stage applies
  the rule to every cell, so the background evolves with the rule (Rule 29 maps 000 to ON), as
  CellularAutomaton[rule, {{1},0}, ...] does in the entry's program.
* Reading convention: a(n) reads the cells -n..n of stage n as a binary number with the leftmost
  cell most significant, as the entry's program does (Take the middle 2n+1 cells, FromDigits base
  2).
* The statement is the conjunction of the 2 conjectures of the site's problem, in the entry's order.
  The closed forms are stated in the rationals, where every division is exact.
* Not part of the site's problem, so not stated here: the formula line by Vincenzo Librandi; the
  formula line by Colin Barker.
* Controls proved in the proof file (theorem controls): the definition gives a(n) for n = 0..21
  equal to the entry's first 22 terms, 1, 3, 4, 111, 16, 1983, 64, 32511, 256, 523263, 1024,
  8384511, ....
-/

namespace OMA.S_oeis_a266516

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

/-- A266516(n). -/
def a (n : ℕ) : ℕ := rowValue (state 29 n) n

/-- Keller's closed forms. -/
theorem main :
    (∀ n : ℕ, Odd n → (a n : ℚ) = 2 * (4 ^ n - 2 ^ n) - 1) ∧
    (∀ n : ℕ, Even n → (a n : ℚ) = 2 ^ n) := by
  sorry

end OMA.S_oeis_a266516

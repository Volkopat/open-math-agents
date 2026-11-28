import Mathlib

/-!
# OEIS A267526: Barker's recurrence and g.f. and Keller's closed form for Rule 141

Source: https://oeis.org/A267526 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry A267526 (Robert Price, Jan 16 2016), offset 0: Binary representation of the n-th iteration of
the Rule 141 elementary cellular automaton starting with a single ON (black) cell.
Formula section:
Conjectures from Colin Barker, Jan 16 2016:
a(n) = 11*a(n-1) + 9990*a(n-2) - 110000*a(n-3) + 100000*a(n-4) for n > 5.
G.f.: (1 - x - 9999*x^2 + 10000*x^3 + 990000*x^4 - 1000000*x^5) /
((1-x)*(1-10*x)*(1-100*x)*(1+100*x)). - [corrected by Karl V. Keller, Jr., Sep 18 2021]
Conjecture: a(n) = 10^n*(100^floor(n/2) - 1)/99 + (10^(n-1) - 1)/9 for n > 1. - Karl V. Keller, Jr.,
Sep 22 2021

Formalization notes:
* Rule numbering: Wolfram's numbering of elementary cellular automata; the new value of cell x is
  bit 4l + 2c + r of the rule number, where l, c, r are the old values of cells x-1, x, x+1.
* Initial condition: at stage 0 cell 0 is ON and every other cell of Z is OFF; each stage applies
  the rule to every cell, so the background evolves with the rule (Rule 141 maps 000 to ON), as
  CellularAutomaton[rule, {{1},0}, ...] does in the entry's program.
* Reading convention: a(n) writes the cells -n..n of stage n as a string of binary digits, leftmost
  cell first, and reads the string as a decimal number (leading OFF cells contribute leading zeros),
  as the entry's program does (Take the middle 2n+1 cells, FromDigits in base 10).
* The statement is the conjunction of the 3 conjectures of the site's problem, in the entry's order.
  The recurrence is stated in the integers. The closed form is stated in the rationals, where every
  division is exact. The generating function is A(x) = Sum_{n >= 0} a(n) x^n in the formal power
  series ring over the rationals, and the identity is A = N * D⁻¹, where D has a nonzero constant
  term.
* In exponents, n - k is natural-number subtraction; it is exact in the stated range.
* floor(n/2) is written n / 2, natural-number division (which rounds down).
* Controls proved in the proof file (theorem controls): the definition gives a(n) for n = 0..20; the
  first 16 of these values are all the entry's listed terms, 1, 10, 101, 1011, 1010111, 10101111,
  10101011111, 101010111111, 101010101111111, 1010101011111111, 1010101010111111111,
  10101010101111111111, ....
-/

namespace OMA.S_oeis_a267526

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

/-- A267526(n). -/
def a (n : ℕ) : ℕ := rowDigits (state 141 n) n

/-- The generating function Sum_{n >= 0} a(n) x^n. -/
noncomputable def A : ℚ⟦X⟧ := PowerSeries.mk fun n => (a n : ℚ)

/-- Barker's recurrence and generating function and Keller's closed form. -/
theorem main :
    (∀ n : ℕ, 5 < n →
      (a n : ℤ) = 11 * a (n - 1) + 9990 * a (n - 2) - 110000 * a (n - 3) + 100000 * a (n - 4)) ∧
    A = (1 - X - 9999 * X ^ 2 + 10000 * X ^ 3 + 990000 * X ^ 4 - 1000000 * X ^ 5) *
      ((1 - X) * (1 - 10 * X) * (1 - 100 * X) * (1 + 100 * X))⁻¹ ∧
    (∀ n : ℕ, 1 < n → (a n : ℚ) = 10 ^ n * (100 ^ (n / 2) - 1) / 99 + (10 ^ (n - 1) - 1) / 9) := by
  sorry

end OMA.S_oeis_a267526

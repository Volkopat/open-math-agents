import Mathlib

/-!
# OEIS A266589: Barker's recurrence and g.f. and Keller's closed forms for Rule 37

Source: https://oeis.org/A266589 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry A266589 (Robert Price, Jan 01 2016), offset 0: Binary representation of the n-th iteration of
the Rule 37 elementary cellular automaton starting with a single ON (black) cell.
Formula section:
Conjectures from Colin Barker, Jan 01 2016 and Apr 18 2019:
a(n) = 10101*a(n-2)-1010100*a(n-4)+1000000*a(n-6) for n>7.
G.f.: (1 +10*x -8991*x^2 +898991*x^3 -10091010*x^4 +1009091010*x^5 +10100000*x^6 -1010100000*x^7) /
((1 -x)*(1 +x)*(1 -10*x)*(1 +10*x)*(1 -100*x)*(1 +100*x)).
Conjecture: a(n) = (10*100^n - 99999*10^(n-2) - 1)/9 for odd n > 1; a(n) = 111*10^(n-1) for even n >
1. - Karl V. Keller, Jr., Oct 06 2021

Formalization notes:
* Rule numbering: Wolfram's numbering of elementary cellular automata; the new value of cell x is
  bit 4l + 2c + r of the rule number, where l, c, r are the old values of cells x-1, x, x+1.
* Initial condition: at stage 0 cell 0 is ON and every other cell of Z is OFF; each stage applies
  the rule to every cell, so the background evolves with the rule (Rule 37 maps 000 to ON), as
  CellularAutomaton[rule, {{1},0}, ...] does in the entry's program.
* Reading convention: a(n) writes the cells -n..n of stage n as a string of binary digits, leftmost
  cell first, and reads the string as a decimal number (leading OFF cells contribute leading zeros),
  as the entry's program does (Take the middle 2n+1 cells, FromDigits in base 10).
* The statement is the conjunction of the 4 conjectures of the site's problem, in the entry's order.
  The recurrence is stated in the integers. The closed forms are stated in the rationals, where
  every division is exact. The generating function is A(x) = Sum_{n >= 0} a(n) x^n in the formal
  power series ring over the rationals, and the identity is A = N * D⁻¹, where D has a nonzero
  constant term.
* In exponents, n - k is natural-number subtraction; it is exact in the stated range.
* Controls proved in the proof file (theorem controls): the definition gives a(n) for n = 0..23; the
  first 17 of these values are all the entry's listed terms, 1, 10, 1110, 1000001, 111000,
  11100000111, 11100000, 111110000011111, 1110000000, 1111111000001111111, 111000000000,
  11111111100000111111111, ....
-/

namespace OMA.S_oeis_a266589

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

/-- A266589(n). -/
def a (n : ℕ) : ℕ := rowDigits (state 37 n) n

/-- The generating function Sum_{n >= 0} a(n) x^n. -/
noncomputable def A : ℚ⟦X⟧ := PowerSeries.mk fun n => (a n : ℚ)

/-- Barker's recurrence and generating function and Keller's closed forms. -/
theorem main :
    (∀ n : ℕ, 7 < n → (a n : ℤ) = 10101 * a (n - 2) - 1010100 * a (n - 4) + 1000000 * a (n - 6)) ∧
    A = (1 + 10 * X - 8991 * X ^ 2 + 898991 * X ^ 3 - 10091010 * X ^ 4 + 1009091010 * X ^ 5 + 10100000 * X ^ 6 - 1010100000 * X ^ 7) *
      ((1 - X) * (1 + X) * (1 - 10 * X) * (1 + 10 * X) * (1 - 100 * X) * (1 + 100 * X))⁻¹ ∧
    (∀ n : ℕ, 1 < n → Odd n → (a n : ℚ) = (10 * 100 ^ n - 99999 * 10 ^ (n - 2) - 1) / 9) ∧
    (∀ n : ℕ, 1 < n → Even n → (a n : ℚ) = 111 * 10 ^ (n - 1)) := by
  sorry

end OMA.S_oeis_a266589

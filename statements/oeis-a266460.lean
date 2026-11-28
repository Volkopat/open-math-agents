import Mathlib

/-!
# OEIS A266460: Barker's recurrence and generating function and Keller's closed form for Rule 27

Source: https://oeis.org/A266460 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry A266460 (Robert Price, Dec 29 2015), offset 0: Binary representation of the n-th iteration
of the Rule 27 elementary cellular automaton starting with a single ON (black) cell.
Formula section:
Conjectures from Colin Barker, Dec 31 2015 and Apr 16 2019:
a(n) = 10011*a(n-2)-110010*a(n-4)+100000*a(n-6) for n>5.
G.f.: (1+101*x-10001*x^2+99900*x^3+10000*x^4-110000*x^5) /
((1-x)*(1+x)*(1-100*x)*(1+100*x)*(1-10*x^2)).
Conjecture: a(n) = (10*(100^n - 9*10^floor(n/2)) - 1)/9 for odd n; a(n) = 10^(n/2) for even n.
- Karl V. Keller, Jr., Sep 29 2021

Formalization notes:
* Rule numbering: Wolfram's numbering of elementary cellular automata; the new value of cell x is
  bit 4l + 2c + r of the rule number, where l, c, r are the old values of cells x-1, x, x+1.
* Initial condition: at stage 0 cell 0 is ON and every other cell of Z is OFF; each stage applies
  the rule to every cell, so the background evolves with the rule (Rule 27 maps 000 to ON), as
  CellularAutomaton[rule, {{1},0}, ...] does in the entry's program.
* Reading convention: a(n) writes the cells -n..n of stage n as a string of binary digits, leftmost
  cell first, and reads the string as a decimal number, as the entry's program does (Take the
  middle 2n+1 cells, FromDigits in base 10); leading OFF cells contribute leading zeros.
* The statement is the conjunction of the three conjectures. The recurrence is stated in the
  integers. The generating function is A(x) = Sum_{n >= 0} a(n) x^n in the formal power series
  ring over the rationals, and the identity is A = N * D⁻¹, where D has constant term 1. Keller's
  odd case is stated in the rationals, with the division by 9 exact there; floor(n/2) and n/2 are
  natural-number division.
* Controls proved in the proof file: the definition gives 1, 101, 10, 1111011, 100, 11111110111,
  1000, 111111111101111, 10000, 1111111111111011111 for n = 0..9, the entry's first terms.
-/

namespace OMA.S_oeis_a266460

open PowerSeries

/-- One step of an elementary cellular automaton in Wolfram's numbering: the new value of cell `x`
is bit `4l + 2c + r` of `rule`, where `l, c, r` are the old values of cells `x-1, x, x+1`. -/
def step (rule : ℕ) (s : ℤ → Bool) (x : ℤ) : Bool :=
  Nat.testBit rule (4 * (s (x - 1)).toNat + 2 * (s x).toNat + (s (x + 1)).toNat)

/-- The automaton started from a single ON cell at `0`. -/
def state (rule : ℕ) : ℕ → ℤ → Bool
  | 0 => fun x => decide (x = 0)
  | n + 1 => step rule (state rule n)

/-- Row `n` (cells `-n..n`) written as binary digits, leftmost cell first, read in base 10. -/
def rowDigits (s : ℤ → Bool) (n : ℕ) : ℕ :=
  ∑ i ∈ Finset.range (2 * n + 1), (s ((n : ℤ) - i)).toNat * 10 ^ i

/-- A266460(n). -/
def a (n : ℕ) : ℕ := rowDigits (state 27 n) n

/-- The generating function `Sum a(n) x^n`. -/
noncomputable def A : ℚ⟦X⟧ := PowerSeries.mk fun n => (a n : ℚ)

/-- Barker's recurrence and generating function, and Keller's closed form. -/
theorem main :
    (∀ n : ℕ, 5 < n → (a n : ℤ) = 10011 * a (n - 2) - 110010 * a (n - 4) + 100000 * a (n - 6)) ∧
    A = (1 + 101 * X - 10001 * X ^ 2 + 99900 * X ^ 3 + 10000 * X ^ 4 - 110000 * X ^ 5) *
      ((1 - X) * (1 + X) * (1 - 100 * X) * (1 + 100 * X) * (1 - 10 * X ^ 2))⁻¹ ∧
    (∀ n : ℕ, Odd n → (a n : ℚ) = (10 * (100 ^ n - 9 * 10 ^ (n / 2)) - 1) / 9) ∧
    (∀ n : ℕ, Even n → a n = 10 ^ (n / 2)) := by
  sorry

end OMA.S_oeis_a266460

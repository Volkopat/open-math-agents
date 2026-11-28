import Mathlib

/-!
# OEIS A266610: Barker's recurrence and g.f. and Keller's closed forms for Rule 41

Source: https://oeis.org/A266610 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry A266610 (Robert Price, Jan 01 2016), offset 0: Decimal representation of the n-th iteration of
the Rule 41 elementary cellular automaton starting with a single ON (black) cell.
Formula section:
Conjectures from Colin Barker, Jan 02 2016 and Apr 18 2019:
a(n) = 16*a(n-2)+a(n-4)-16*a(n-6) for n>5.
G.f.: (1-11*x^2+100*x^3-80*x^4+440*x^5) / ((1-x)*(1+x)*(1-4*x)*(1+4*x)*(1+x^2)).
Conjecture: a(n) = 2*4^n + 2 - 10*(n mod 4) for odd n; a(n) = 5^((n mod 4)/2) for even n. - Karl V.
Keller, Jr., Oct 07 2021

Formalization notes:
* Rule numbering: Wolfram's numbering of elementary cellular automata; the new value of cell x is
  bit 4l + 2c + r of the rule number, where l, c, r are the old values of cells x-1, x, x+1.
* Initial condition: at stage 0 cell 0 is ON and every other cell of Z is OFF; each stage applies
  the rule to every cell, so the background evolves with the rule (Rule 41 maps 000 to ON), as
  CellularAutomaton[rule, {{1},0}, ...] does in the entry's program.
* Reading convention: a(n) reads the cells -n..n of stage n as a binary number with the leftmost
  cell most significant, as the entry's program does (Take the middle 2n+1 cells, FromDigits base
  2).
* The statement is the conjunction of the 4 conjectures of the site's problem, in the entry's order.
  The recurrence is stated in the integers. The closed forms are stated in the rationals, where
  every division is exact. The generating function is A(x) = Sum_{n >= 0} a(n) x^n in the formal
  power series ring over the rationals, and the identity is A = N * D⁻¹, where D has a nonzero
  constant term.
* n mod 4 is n % 4 in the natural numbers, cast to the rationals where it multiplies, and (n mod
  4)/2 in an exponent is natural-number division, exact for even n.
* Controls proved in the proof file (theorem controls): the definition gives a(n) for n = 0..25
  equal to the entry's first 26 terms, 1, 0, 5, 100, 1, 2040, 5, 32740, 1, 524280, 5, 8388580, ....
-/

namespace OMA.S_oeis_a266610

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

/-- A266610(n). -/
def a (n : ℕ) : ℕ := rowValue (state 41 n) n

/-- The generating function Sum_{n >= 0} a(n) x^n. -/
noncomputable def A : ℚ⟦X⟧ := PowerSeries.mk fun n => (a n : ℚ)

/-- Barker's recurrence and generating function and Keller's closed forms. -/
theorem main :
    (∀ n : ℕ, 5 < n → (a n : ℤ) = 16 * a (n - 2) + a (n - 4) - 16 * a (n - 6)) ∧
    A = (1 - 11 * X ^ 2 + 100 * X ^ 3 - 80 * X ^ 4 + 440 * X ^ 5) *
      ((1 - X) * (1 + X) * (1 - 4 * X) * (1 + 4 * X) * (1 + X ^ 2))⁻¹ ∧
    (∀ n : ℕ, Odd n → (a n : ℚ) = 2 * 4 ^ n + 2 - 10 * ((n % 4 : ℕ) : ℚ)) ∧
    (∀ n : ℕ, Even n → (a n : ℚ) = 5 ^ ((n % 4) / 2)) := by
  sorry

end OMA.S_oeis_a266610

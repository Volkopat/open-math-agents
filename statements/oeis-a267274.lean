import Mathlib

/-!
# OEIS A267274: Barker's closed form, recurrence and g.f. for the decimal rows of Rule 117

Source: https://oeis.org/A267274 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry A267274 (Robert Price, Jan 12 2016), offset 0: Decimal representation of the n-th iteration of
the Rule 117 elementary cellular automaton starting with a single ON (black) cell.
Formula section:
Conjectures from Colin Barker, Jan 14 2016 and Apr 19 2019:
a(n) = ((-4)^n+(-1)^n+2^(2*n+1)-1)/2 = A266984(n) for n>1.
a(n) = 17*a(n-2)-16*a(n-4) for n>5.
G.f.: (1+3*x+7*x^2-20*x^3-8*x^4+32*x^5) / ((1-x)*(1+x)*(1-4*x)*(1+4*x)).

Formalization notes:
* Rule numbering: Wolfram's numbering of elementary cellular automata; the new value of cell x is
  bit 4l + 2c + r of the rule number, where l, c, r are the old values of cells x-1, x, x+1.
* Initial condition: at stage 0 cell 0 is ON and every other cell of Z is OFF; each stage applies
  the rule to every cell, so the background evolves with the rule (Rule 117 maps 000 to ON), as
  CellularAutomaton[rule, {{1},0}, ...] does in the entry's program.
* Reading convention: a(n) reads the cells -n..n of stage n as a binary number with the leftmost
  cell most significant, as the entry's program does (Take the middle 2n+1 cells, FromDigits base
  2).
* A266984 is, by its name (Decimal representation of the n-th iteration of the Rule 81 elementary
  cellular automaton starting with a single ON (black) cell), the sequence b (the same reading of
  Rule 81); its listed terms a(0..18) = 1, 1, 24, 31, 384, 511, 6144, 8191, 98304, 131071, 1572864,
  2097151, ... are controls (theorem controls_A266984).
* The statement is the conjunction of the 4 conjectures of the site's problem, in the entry's order.
  The recurrence is stated in the integers. The closed form is stated in the rationals, where every
  division is exact. The generating function is A(x) = Sum_{n >= 0} a(n) x^n in the formal power
  series ring over the rationals, and the identity is A = N * D⁻¹, where D has a nonzero constant
  term.
* Controls proved in the proof file (theorem controls): the definition gives a(n) for n = 0..19
  equal to the entry's first 20 terms, 1, 3, 24, 31, 384, 511, 6144, 8191, 98304, 131071, 1572864,
  2097151, ....
-/

namespace OMA.S_oeis_a267274

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

/-- A267274(n). -/
def a (n : ℕ) : ℕ := rowValue (state 117 n) n

/-- A266984(n): the same reading for Rule 81, as the name of A266984 says. -/
def b (n : ℕ) : ℕ := rowValue (state 81 n) n

/-- The generating function Sum_{n >= 0} a(n) x^n. -/
noncomputable def A : ℚ⟦X⟧ := PowerSeries.mk fun n => (a n : ℚ)

/-- Barker's closed form, recurrence and generating function. -/
theorem main :
    (∀ n : ℕ, 1 < n → (a n : ℚ) = ((-4) ^ n + (-1) ^ n + 2 ^ (2 * n + 1) - 1) / 2) ∧
    (∀ n : ℕ, 1 < n → a n = b n) ∧
    (∀ n : ℕ, 5 < n → (a n : ℤ) = 17 * a (n - 2) - 16 * a (n - 4)) ∧
    A = (1 + 3 * X + 7 * X ^ 2 - 20 * X ^ 3 - 8 * X ^ 4 + 32 * X ^ 5) *
      ((1 - X) * (1 + X) * (1 - 4 * X) * (1 + 4 * X))⁻¹ := by
  sorry

end OMA.S_oeis_a267274

import Mathlib

/-!
# OEIS A265431: Barker's closed form and generating function for the total OFF cells of Rule 188

Source: https://oeis.org/A265431 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry A265431 (Robert Price, Dec 08 2015), offset 0: Total number of OFF (white) cells after n
iterations of the Rule 188 elementary cellular automaton starting with a single ON (black) cell.
Formula section:
Conjectures from Colin Barker, Dec 09 2015 and Apr 16 2019:
a(n) = 1/16*(10*n^2+8*n+3*(-1)^n-2*(-i)^n-2*i^n+1) where i = sqrt(-1).
G.f.: x*(1+2*x+2*x^3) / ((1-x)^3*(1+x)*(1+x^2)).

Formalization notes:
* Rule numbering: Wolfram's numbering of elementary cellular automata; the new value of cell x is
  bit 4l + 2c + r of the rule number, where l, c, r are the old values of cells x-1, x, x+1.
* Initial condition: at stage 0 cell 0 is ON and every other cell of Z is OFF; each stage applies
  the rule to every cell, so the background evolves with the rule (Rule 188 maps 000 to OFF, so it
  stays OFF), as CellularAutomaton[rule, {{1},0}, ...] does in the entry's program.
* Counting convention: a(n) is the sum over the stages k = 0..n of the number of OFF cells among the
  cells -k..k of stage k; this reading reproduces the entry's listed terms (controls below).
* The statement is the conjunction of the 2 conjectures of the site's problem, in the entry's order.
  The closed form with i = sqrt(-1) is stated in the complex numbers, with Complex.I for i. The
  generating function is A(x) = Sum_{n >= 0} a(n) x^n in the formal power series ring over the
  rationals, and the identity is A = N * D⁻¹, where D has a nonzero constant term.
* Controls proved in the proof file (theorem controls): the definition gives a(n) for n = 0..26
  equal to the entry's first 27 terms, 0, 1, 4, 7, 12, 18, 26, 34, 44, 55, 68, 81, ....
-/

namespace OMA.S_oeis_a265431

open PowerSeries

/-- One step of an elementary cellular automaton in Wolfram's numbering. -/
def step (rule : ℕ) (s : ℤ → Bool) (x : ℤ) : Bool :=
  Nat.testBit rule (4 * (s (x - 1)).toNat + 2 * (s x).toNat + (s (x + 1)).toNat)

/-- The automaton started from a single ON cell at 0. -/
def state (rule : ℕ) : ℕ → ℤ → Bool
  | 0 => fun x => decide (x = 0)
  | n + 1 => step rule (state rule n)

/-- The number of OFF cells of row n among the cells -n..n. -/
def offCount (s : ℤ → Bool) (n : ℕ) : ℕ :=
  ∑ i ∈ Finset.range (2 * n + 1), (!s ((n : ℤ) - i)).toNat

/-- A265431(n): the total number of OFF cells in rows 0..n. -/
def a (n : ℕ) : ℕ := ∑ k ∈ Finset.range (n + 1), offCount (state 188 k) k

/-- The generating function Sum_{n >= 0} a(n) x^n. -/
noncomputable def A : ℚ⟦X⟧ := PowerSeries.mk fun n => (a n : ℚ)

/-- Barker's closed form and generating function. -/
theorem main :
    (∀ n : ℕ, (a n : ℂ) = 1/16*(10*(n : ℂ)^2+8*(n : ℂ)+3*(-1)^n-2*(-Complex.I)^n-2*Complex.I^n+1)) ∧
    A = (X * (1 + 2 * X + 2 * X ^ 3)) * ((1 - X) ^ 3 * (1 + X) * (1 + X ^ 2))⁻¹ := by
  sorry

end OMA.S_oeis_a265431

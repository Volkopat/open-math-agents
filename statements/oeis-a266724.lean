import Mathlib

/-!
# OEIS A266724: Barker's closed form, recurrence and generating function for Rule 59

Source: https://oeis.org/A266724 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry A266724 (Robert Price, Jan 03 2016), offset 0: Number of OFF (white) cells in the n-th
iteration of the Rule 59 elementary cellular automaton starting with a single ON (black) cell.
Formula section:
Conjectures from Colin Barker, Jan 05 2016 and Apr 18 2019:
a(n) = (-1)^n*(n-1)+n for n>0.
a(n) = 2*a(n-2)-a(n-4) for n>4.
G.f.: x*(1+3*x-x^2+x^3) / ((1-x)^2*(1+x)^2).

Formalization notes:
* Rule numbering: Wolfram's numbering of elementary cellular automata; the new value of cell x is
  bit 4l + 2c + r of the rule number, where l, c, r are the old values of cells x-1, x, x+1.
* Initial condition: at stage 0 cell 0 is ON and every other cell of Z is OFF; each stage applies
  the rule to every cell, so the background evolves with the rule (Rule 59 maps 000 to ON), as
  CellularAutomaton[rule, {{1},0}, ...] does in the entry's program.
* Counting convention: a(n) counts the OFF cells among the cells -n..n of stage n, the 2n+1 cells
  the entry's program keeps (Take the middle 2n+1 cells; their length minus their ON count).
* The statement is the conjunction of the three conjectures. The closed form and the recurrence
  are stated in the integers. The generating function is A(x) = Sum_{n >= 0} a(n) x^n in the
  formal power series ring over the rationals, and the identity is A = N * D⁻¹, where D has
  constant term 1.
* Controls proved in the proof file: the definition gives 0, 1, 3, 1, 7, 1, 11, 1, 15, 1, 19, 1,
  23, 1, 27, 1 for n = 0..15, the entry's first terms.
-/

namespace OMA.S_oeis_a266724

open PowerSeries

/-- One step of an elementary cellular automaton in Wolfram's numbering: the new value of cell `x`
is bit `4l + 2c + r` of `rule`, where `l, c, r` are the old values of cells `x-1, x, x+1`. -/
def step (rule : ℕ) (s : ℤ → Bool) (x : ℤ) : Bool :=
  Nat.testBit rule (4 * (s (x - 1)).toNat + 2 * (s x).toNat + (s (x + 1)).toNat)

/-- The automaton started from a single ON cell at `0`. -/
def state (rule : ℕ) : ℕ → ℤ → Bool
  | 0 => fun x => decide (x = 0)
  | n + 1 => step rule (state rule n)

/-- The number of OFF cells of row `n` among the cells `-n..n` (cell `n - i` for `i < 2n + 1`). -/
def offCount (s : ℤ → Bool) (n : ℕ) : ℕ :=
  ((Finset.range (2 * n + 1)).filter fun i : ℕ => s ((n : ℤ) - i) = false).card

/-- A266724(n). -/
def a (n : ℕ) : ℕ := offCount (state 59 n) n

/-- The generating function `Sum a(n) x^n`. -/
noncomputable def A : ℚ⟦X⟧ := PowerSeries.mk fun n => (a n : ℚ)

/-- Barker's closed form, recurrence and generating function. -/
theorem main :
    (∀ n : ℕ, 0 < n → (a n : ℤ) = (-1) ^ n * ((n : ℤ) - 1) + n) ∧
    (∀ n : ℕ, 4 < n → (a n : ℤ) = 2 * a (n - 2) - a (n - 4)) ∧
    A = X * (1 + 3 * X - X ^ 2 + X ^ 3) * ((1 - X) ^ 2 * (1 + X) ^ 2)⁻¹ := by
  sorry

end OMA.S_oeis_a266724

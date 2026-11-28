import Mathlib

/-!
# A267884: Total number of OFF (white) cells after n iterations of the "Rule 233" elementary cellular automaton starting with a single ON (black) cell

Source: https://oeis.org/A267884 (OEIS Foundation, CC BY-SA 4.0).
Credit: @Mapika (AI-assisted: Claude Code, model claude-opus-5-5).

Entry A267884 (Robert Price, Jan 21 2016), offset 0. Formula section, verbatim:
Conjectures from Colin Barker, Jan 24 2016 and Apr 20 2019:
a(n) = 6 for n>2.
a(n) = a(n-1) for n>3.
G.f.: x*(3+2*x+x^2) / (1-x).

Formalization notes:
* Rule numbering: Wolfram's numbering of elementary cellular automata; the new value of cell x is
  bit 4l + 2c + r of the rule number, where l, c, r are the old values of cells x-1, x, x+1.
* Initial condition: at stage 0 cell 0 is ON and every other cell of Z is OFF; each stage applies
  the rule to every cell, so the background evolves with the rule (Rule 233 maps 000 to ON).
* Counting convention: stage k contributes the number of OFF cells among its cells -k..k (the
  middle 2k+1 cells, as in the entry's program), and a(n) is the total of these numbers over the
  stages k = 0..n (the entry's program takes the partial sums of the per-stage white counts).
* The statement is the conjunction of the three conjectures, on the ranges the entry gives.
  The generating function is A(x) = Sum_{n >= 0} a(n) x^n in the formal power series ring over
  the rationals, and the identity is A = N * D⁻¹, where D = 1-x has constant term 1.
* Controls from the entry: the definition gives 0, 3, 5, 6, 6, 6, 6 for n = 0..6, matching the
  entry's data.
-/

namespace OMA.S_oeis_a267884

open PowerSeries

/-- One step of an elementary cellular automaton in Wolfram's numbering. -/
def step (rule : ℕ) (s : ℤ → Bool) (x : ℤ) : Bool :=
  Nat.testBit rule (4 * (s (x - 1)).toNat + 2 * (s x).toNat + (s (x + 1)).toNat)

/-- The automaton started from a single ON cell at 0. -/
def state (rule : ℕ) : ℕ → ℤ → Bool
  | 0 => fun x => decide (x = 0)
  | n + 1 => step rule (state rule n)

/-- The number of OFF cells among the cells -n..n of a row. -/
def offCount (s : ℤ → Bool) (n : ℕ) : ℕ :=
  ∑ i ∈ Finset.range (2 * n + 1), (!s ((n : ℤ) - i)).toNat

/-- A267884(n): the total number of OFF cells in stages 0..n of Rule 233. -/
def a (n : ℕ) : ℕ := ∑ k ∈ Finset.range (n + 1), offCount (state 233 k) k

/-- The generating function Sum_{n >= 0} a(n) x^n. -/
noncomputable def A : ℚ⟦X⟧ := PowerSeries.mk fun n => (a n : ℚ)

/-- Barker's closed form, recurrence and generating function for OEIS A267884. -/
theorem main :
    (∀ n : ℕ, 2 < n → a n = 6) ∧
    (∀ n : ℕ, 3 < n → a n = a (n - 1)) ∧
    A = X * (3 + 2 * X + X ^ 2) * (1 - X)⁻¹ := by
  sorry

end OMA.S_oeis_a267884

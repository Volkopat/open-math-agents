import Mathlib

/-!
# OEIS A266723: Barker's conjectures for the total number of ON cells of Rule 59

Source: https://oeis.org/A266723 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry A266723 (Robert Price, Jan 03 2016), offset 0: Total number of ON (black) cells after n
iterations of the Rule 59 elementary cellular automaton starting with a single ON (black) cell.
Formula section:
Conjectures from Colin Barker, Jan 05 2016 and Apr 18 2019:
a(n) = (3+(-1)^n-2*(-3+(-1)^n)*n+2*n^2)/4.
a(n) = a(n-1)+2*a(n-2)-2*a(n-3)-a(n-4)+a(n-5) for n>4.
G.f.: (1+2*x-x^2)*(1+x^2) / ((1-x)^3*(1+x)^2).

Formalization notes:
* Rule numbering: Wolfram's numbering of elementary cellular automata; the new value of cell x is
  bit 4l + 2c + r of the rule number, where l, c, r are the old values of cells x-1, x, x+1.
* Initial condition: at stage 0 cell 0 is ON and every other cell of Z is OFF; each stage applies
  the rule to every cell, so the background evolves with the rule (Rule 59 maps 000 to ON), as
  CellularAutomaton[rule, {{1},0}, ...] does in the entry's program.
* Counting convention: as in the entry's program, stage t counts the ON cells among the cells
  -t..t, and a(n) is the sum of these counts for t = 0..n.
* The statement is the conjunction of the three conjectures. The closed form (stated for every
  n) is written as 4a(n) = 3 + (-1)^n - 2(-3 + (-1)^n)n + 2n^2 in the integers, and the
  recurrence in the integers. Since the denominator of the generating function has constant term
  1, the identity A(x) = N/D for A(x) = Sum_{n >= 0} a(n) x^n is stated as A * D = N in the formal
  power series ring over the integers.
* Controls proved in the proof file: the definition gives 1, 3, 5, 11, 13, 23, 25, 39, 41, 59,
  61, 83, 85, 111, 113, 143 for n = 0..15, the entry's first terms.
-/

namespace OMA.S_oeis_a266723

open PowerSeries

/-- One step of an elementary cellular automaton in Wolfram's numbering: the new value of cell `x`
is bit `4l + 2c + r` of `rule`, where `l, c, r` are the old values of cells `x-1, x, x+1`. -/
def step (rule : ℕ) (s : ℤ → Bool) (x : ℤ) : Bool :=
  Nat.testBit rule (4 * (s (x - 1)).toNat + 2 * (s x).toNat + (s (x + 1)).toNat)

/-- The automaton started from a single ON cell at `0`. -/
def state (rule : ℕ) : ℕ → ℤ → Bool
  | 0 => fun x => decide (x = 0)
  | n + 1 => step rule (state rule n)

/-- The number of ON cells of a row among the cells `-n..n` (cell `n - i` for `i < 2n + 1`). -/
def onCount (s : ℤ → Bool) (n : ℕ) : ℕ :=
  ((Finset.range (2 * n + 1)).filter fun i : ℕ => s ((n : ℤ) - i) = true).card

/-- A266723(n): the total number of ON cells in the stages 0..n. -/
def a (n : ℕ) : ℕ := ∑ t ∈ Finset.range (n + 1), onCount (state 59 t) t

/-- Barker's closed form, recurrence and generating function. -/
theorem main :
    (∀ n : ℕ, 4 * (a n : ℤ) = 3 + (-1) ^ n - 2 * (-3 + (-1) ^ n) * n + 2 * n ^ 2) ∧
    (∀ n : ℕ, 4 < n →
      (a n : ℤ) = a (n - 1) + 2 * a (n - 2) - 2 * a (n - 3) - a (n - 4) + a (n - 5)) ∧
    PowerSeries.mk (fun n => (a n : ℤ)) * ((1 - X) ^ 3 * (1 + X) ^ 2) =
      (1 + 2 * X - X ^ 2) * (1 + X ^ 2) := by
  sorry

end OMA.S_oeis_a266723

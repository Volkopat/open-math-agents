import Mathlib

/-!
# OEIS A266793: Barker's conjectures for the ON cells of Rule 61

Source: https://oeis.org/A266793 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry A266793 (Robert Price, Jan 03 2016), offset 0: Total number of ON (black) cells after n
iterations of the Rule 61 elementary cellular automaton starting with a single ON (black) cell.
Formula section:
Conjectures from Colin Barker, Jan 04 2016 and Apr 18 2019:
a(n) = (1+7*(-1)^n-2*(-3+(-1)^n)*n+2*n^2)/4 for n>3.
a(n) = a(n-1)+2*a(n-2)-2*a(n-3)-a(n-4)+a(n-5) for n>8.
G.f.: (1+2*x+x^3+x^4-x^5-x^6+2*x^7-x^8) / ((1-x)^3*(1+x)^2).

Formalization notes:
* Rule numbering: Wolfram's numbering of elementary cellular automata; the new value of cell i is
  bit 4l + 2c + x of the rule number, where l, c, x are the old values of cells i-1, i, i+1.
* Initial condition: at stage 0 cell 0 is ON and every other cell of Z is OFF; each stage applies
  the rule to every cell, so the background evolves with the rule (Rule 61 maps 000 to ON), as
  CellularAutomaton[rule, {{1},0}, ...] does in the entry's program.
* Counting convention: as in the entry's program, stage t counts the ON cells among the cells
  -t..t, and a(n) is the sum of these counts for t = 0..n.
* The statement is the conjunction of the three conjectures. The closed form is stated for n > 3
  as 4a(n) = 1 + 7(-1)^n - 2(-3 + (-1)^n)n + 2n^2 in the integers, and the recurrence in the
  integers. Since the denominator of the generating function has constant term 1, the identity
  A(x) = N/D for A(x) = Sum_{n >= 0} a(n) x^n is stated as A * D = N in the formal power series
  ring over the integers.
* Controls from the entry, proved in the proof file: a(0..8) = 1, 3, 5, 10, 14, 21, 26, 37, 42.
-/

namespace OMA.S_oeis_a266793

open PowerSeries

/-- Wolfram's elementary rule r applied to a neighborhood (left, center, right). -/
def rule (r : ℕ) (l c x : Bool) : Bool := r.testBit (4 * l.toNat + 2 * c.toNat + x.toNat)

/-- Row n of rule r from a single ON cell at 0, the rule applied to every cell. -/
def row (r : ℕ) : ℕ → ℤ → Bool
  | 0 => fun i => decide (i = 0)
  | n + 1 => fun i => rule r (row r n (i - 1)) (row r n i) (row r n (i + 1))

/-- The number of ON cells among the cells -n..n of row n of Rule 61. -/
def on (n : ℕ) : ℕ :=
  ((Finset.range (2 * n + 1)).filter (fun k : ℕ => row 61 n ((k : ℤ) - n) = true)).card

/-- A266793(n): the total number of ON cells in rows 0..n. -/
def a (n : ℕ) : ℕ := ∑ t ∈ Finset.range (n + 1), on t

/-- Barker's closed form, recurrence and generating function. -/
theorem main :
    (∀ n : ℕ, 3 < n →
      4 * (a n : ℤ) = 1 + 7 * (-1) ^ n - 2 * (-3 + (-1) ^ n) * n + 2 * n ^ 2) ∧
    (∀ n : ℕ, 8 < n →
      (a n : ℤ) = a (n - 1) + 2 * a (n - 2) - 2 * a (n - 3) - a (n - 4) + a (n - 5)) ∧
    PowerSeries.mk (fun n => (a n : ℤ)) * ((1 - X) ^ 3 * (1 + X) ^ 2) =
      1 + 2 * X + X ^ 3 + X ^ 4 - X ^ 5 - X ^ 6 + 2 * X ^ 7 - X ^ 8 := by
  sorry

end OMA.S_oeis_a266793

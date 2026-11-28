import Mathlib

/-!
# OEIS A266221: Barker's conjectures for the ON cells of Rule 7

Source: https://oeis.org/A266221 (Colin Barker, Dec 25 2015 and Apr 13 2019)

Entry A266221 (Robert Price, Dec 24 2015), offset 0: Total number of ON (black) cells after n iterations of the Rule 7 elementary cellular automaton starting with a single ON (black) cell.
Formula section:
Conjectures from Colin Barker, Dec 25 2015 and Apr 13 2019: (Start)
a(n) = 1/2*(n+1)*(n-(-1)^n+1).
a(n) = a(n-1)+2*a(n-2)-2*a(n-3)-a(n-4)+a(n-5) for n>5.
G.f.: (1+2*x-2*x^2+3*x^3+x^4-x^5) / ((1-x)^3*(1+x)^2).
(End)

Formalization notes:
* Rule numbering: Wolfram's numbering of elementary cellular automata; the new value of cell i is
  bit 4l + 2c + r of the rule number, where l, c, r are the old values of cells i-1, i, i+1.
* Initial condition: at stage 0 cell 0 is ON and every other cell of Z is OFF; each stage applies
  the rule to every cell (Rule 7 maps 000 to ON and 111 to OFF, so the background alternates between OFF and ON), as CellularAutomaton[rule, {{1},0}, ...] does
  in the entry's program.
* Counting convention: as in the entry's program, stage t counts the ON cells among the cells
  -t..t, and a(n) is the sum of these counts for t = 0..n.
* The statement is the conjunction of Barker's closed form, recurrence and generating function.
* The closed form has no stated range, but it fails at n = 0 (it gives 0, while a(0) = 1), so it is stated for n > 0, where it is meant; it is multiplied by 2 and stated in the integers.
* The recurrence is stated in the integers. Since the denominator of the generating function has
  constant term 1, the identity A(x) = N/D for A(x) = Sum_(n >= 0) a(n) x^n is stated as A * D = N
  in the formal power series ring over the integers.
* Controls from the entry: the definition gives 1, 3, 3, 10, 10, 21, 21, 36, 36, 55 for n = 0..9.
-/

namespace OMA.S_oeis_a266221

open PowerSeries

/-- Wolfram's code: the new cell is bit 4l + 2c + r of the rule number. -/
def eca (rule : ℕ) (l c r : Bool) : Bool := Nat.testBit rule (4 * l.toNat + 2 * c.toNat + r.toNat)

/-- Stage t of Rule 7 from a single ON cell at 0. -/
def state : ℕ → ℤ → Bool
  | 0, i => decide (i = 0)
  | t + 1, i => eca 7 (state t (i - 1)) (state t i) (state t (i + 1))

/-- The number of ON cells of stage t among the cells -t..t. -/
def black (t : ℕ) : ℕ :=
  ((Finset.range (2 * t + 1)).filter fun i : ℕ => state t ((i : ℤ) - (t : ℤ))).card

/-- A266221(n): the total number of ON cells in stages 0..n. -/
def a (n : ℕ) : ℕ := ∑ t ∈ Finset.range (n + 1), black t

/-- Barker's closed form, recurrence and generating function. -/
theorem main :
    (∀ n : ℕ, 0 < n → 2 * (a n : ℤ) = (n + 1) * (n - (-1) ^ n + 1)) ∧
    (∀ n : ℕ, 5 < n →
      (a n : ℤ) = a (n - 1) + 2 * a (n - 2) - 2 * a (n - 3) - a (n - 4) + a (n - 5)) ∧
    mk (fun n => (a n : ℤ)) * ((1 - X) ^ 3 * (1 + X) ^ 2) =
      (1 + 2 * X - 2 * X ^ 2 + 3 * X ^ 3 + X ^ 4 - X ^ 5 : PowerSeries ℤ) := by
  sorry

end OMA.S_oeis_a266221

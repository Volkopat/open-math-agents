import Mathlib

/-!
# OEIS A266437: Barker's conjectures for the ON cells of Rule 23

Source: https://oeis.org/A266437 (Colin Barker, Dec 30 2015 and Apr 15 2019)

Entry A266437 (Robert Price, Dec 29 2015), offset 0: Number of ON (black) cells in the n-th iteration of the Rule 23 elementary cellular automaton starting with a single ON (black) cell.
Formula section:
Empirical g.f.: (1 + 3*x - 2*x^2 + x^3 + x^4)/(-1 + x^2)^2. - Michael De Vlieger, Dec 29 2015
Conjectures from Colin Barker, Dec 30 2015 and Apr 15 2019: (Start)
a(n) = (1-(-1)^n)*(2*n+1)/2 for n>0.
a(n) = 2*a(n-2)-a(n-4) for n>4.

Formalization notes:
* Rule numbering: Wolfram's numbering of elementary cellular automata; the new value of cell i is
  bit 4l + 2c + r of the rule number, where l, c, r are the old values of cells i-1, i, i+1.
* Initial condition: at stage 0 cell 0 is ON and every other cell of Z is OFF; each stage applies
  the rule to every cell (Rule 23 maps 000 to ON and 111 to OFF, so the background alternates between OFF and ON), as CellularAutomaton[rule, {{1},0}, ...] does
  in the entry's program.
* Counting convention: as in the entry's program, stage t counts the ON cells among the cells
  -t..t, and a(n) is the count for stage n.
* The statement is the conjunction of De Vlieger's empirical generating function, Barker's closed form and Barker's recurrence.
* The closed form is stated for n > 0 (as in the entry) after multiplying both sides by 2, in the integers.
* The recurrence is stated in the integers. Since the denominator of the generating function has
  constant term 1, the identity A(x) = N/D for A(x) = Sum_(n >= 0) a(n) x^n is stated as A * D = N
  in the formal power series ring over the integers.
* Controls from the entry: the definition gives 1, 3, 0, 7, 0, 11, 0, 15, 0, 19 for n = 0..9.
-/

namespace OMA.S_oeis_a266437

open PowerSeries

/-- Wolfram's code: the new cell is bit 4l + 2c + r of the rule number. -/
def eca (rule : ℕ) (l c r : Bool) : Bool := Nat.testBit rule (4 * l.toNat + 2 * c.toNat + r.toNat)

/-- Stage t of Rule 23 from a single ON cell at 0. -/
def state : ℕ → ℤ → Bool
  | 0, i => decide (i = 0)
  | t + 1, i => eca 23 (state t (i - 1)) (state t i) (state t (i + 1))

/-- The number of ON cells of stage t among the cells -t..t. -/
def black (t : ℕ) : ℕ :=
  ((Finset.range (2 * t + 1)).filter fun i : ℕ => state t ((i : ℤ) - (t : ℤ))).card

/-- A266437(n): the number of ON cells among the cells -n..n of stage n. -/
def a (n : ℕ) : ℕ := black n

/-- De Vlieger's empirical generating function, Barker's closed form and Barker's recurrence. -/
theorem main :
    mk (fun n => (a n : ℤ)) * ((-1 + X ^ 2) ^ 2) =
      (1 + 3 * X - 2 * X ^ 2 + X ^ 3 + X ^ 4 : PowerSeries ℤ) ∧
    (∀ n : ℕ, 0 < n → 2 * (a n : ℤ) = (1 - (-1) ^ n) * (2 * n + 1)) ∧
    (∀ n : ℕ, 4 < n →
      (a n : ℤ) = 2 * a (n - 2) - a (n - 4)) := by
  sorry

end OMA.S_oeis_a266437

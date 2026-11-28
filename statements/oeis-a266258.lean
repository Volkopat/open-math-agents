import Mathlib

/-!
# OEIS A266258: Barker's conjectures for the OFF cells of Rule 11

Source: https://oeis.org/A266258 (Colin Barker, Dec 27 2015 and Apr 14 2019)

Entry A266258 (Robert Price, Dec 25 2015), offset 0: Number of OFF (white) cells in the n-th iteration of the Rule 11 elementary cellular automaton starting with a single ON (black) cell.
Formula section:
Conjectures from Colin Barker, Dec 27 2015 and Apr 14 2019: (Start)
a(n) = (2*(-1)^n*n+2*n-3*(-1)^n+1)/2 for n>0
a(n) = 2*a(n-2)-a(n-4) for n>4.
G.f.: x*(2+3*x-2*x^2+x^3) / ((1-x)^2*(1+x)^2).
(End)

Formalization notes:
* Rule numbering: Wolfram's numbering of elementary cellular automata; the new value of cell i is
  bit 4l + 2c + r of the rule number, where l, c, r are the old values of cells i-1, i, i+1.
* Initial condition: at stage 0 cell 0 is ON and every other cell of Z is OFF; each stage applies
  the rule to every cell (Rule 11 maps 000 to ON and 111 to OFF, so the background alternates between OFF and ON), as CellularAutomaton[rule, {{1},0}, ...] does
  in the entry's program.
* Counting convention: as in the entry's program, stage t counts the OFF cells among the cells
  -t..t, and a(n) is the count for stage n.
* The statement is the conjunction of Barker's closed form, recurrence and generating function.
* The closed form is stated for n > 0 (as in the entry) after multiplying both sides by 2, in the integers.
* The recurrence is stated in the integers. Since the denominator of the generating function has
  constant term 1, the identity A(x) = N/D for A(x) = Sum_(n >= 0) a(n) x^n is stated as A * D = N
  in the formal power series ring over the integers.
* Controls from the entry: the definition gives 0, 2, 3, 2, 7, 2, 11, 2, 15, 2 for n = 0..9.
-/

namespace OMA.S_oeis_a266258

open PowerSeries

/-- Wolfram's code: the new cell is bit 4l + 2c + r of the rule number. -/
def eca (rule : ℕ) (l c r : Bool) : Bool := Nat.testBit rule (4 * l.toNat + 2 * c.toNat + r.toNat)

/-- Stage t of Rule 11 from a single ON cell at 0. -/
def state : ℕ → ℤ → Bool
  | 0, i => decide (i = 0)
  | t + 1, i => eca 11 (state t (i - 1)) (state t i) (state t (i + 1))

/-- The number of OFF cells of stage t among the cells -t..t. -/
def white (t : ℕ) : ℕ :=
  ((Finset.range (2 * t + 1)).filter fun i : ℕ => state t ((i : ℤ) - (t : ℤ)) = false).card

/-- A266258(n): the number of OFF cells among the cells -n..n of stage n. -/
def a (n : ℕ) : ℕ := white n

/-- Barker's closed form, recurrence and generating function. -/
theorem main :
    (∀ n : ℕ, 0 < n → 2 * (a n : ℤ) = 2 * (-1) ^ n * n + 2 * n - 3 * (-1) ^ n + 1) ∧
    (∀ n : ℕ, 4 < n →
      (a n : ℤ) = 2 * a (n - 2) - a (n - 4)) ∧
    mk (fun n => (a n : ℤ)) * ((1 - X) ^ 2 * (1 + X) ^ 2) =
      (X * (2 + 3 * X - 2 * X ^ 2 + X ^ 3) : PowerSeries ℤ) := by
  sorry

end OMA.S_oeis_a266258

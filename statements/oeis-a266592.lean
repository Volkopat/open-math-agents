import Mathlib

/-!
# OEIS A266592: Barker's conjectures for the binary middle column of Rule 37

Source: https://oeis.org/A266592 (Colin Barker, Jan 02 2016 and Apr 18 2019)

Entry A266592 (Robert Price, Jan 01 2016), offset 0: Binary representation of the middle column of the Rule 37 elementary cellular automaton starting with a single ON (black) cell.
Formula section:
Conjectures from Colin Barker, Jan 02 2016 and Apr 18 2019: (Start)
a(n) = (45*(-1)^n+1099*10^n-55)/990 for n>0.
a(n) = 10*a(n-1)+a(n-2)-10*a(n-3) for n>3.
G.f.: (1+x-x^3) / ((1-x)*(1+x)*(1-10*x)).
(End)

Formalization notes:
* Rule numbering: Wolfram's numbering of elementary cellular automata; the new value of cell i is
  bit 4l + 2c + r of the rule number, where l, c, r are the old values of cells i-1, i, i+1.
* Initial condition: at stage 0 cell 0 is ON and every other cell of Z is OFF; each stage applies
  the rule to every cell (Rule 37 maps 000 to ON and 111 to OFF), as
  CellularAutomaton[rule, {{1},0}, ...] does in the entry's program.
* Counting convention: as in the entry's program, the middle cells (cell 0) of stages 0..n are
  written as binary digits, stage 0 first, and read in base 10 (FromDigits of the
  first n+1 middle cells).
* The statement is the conjunction of Barker's closed form, recurrence and generating function. The recurrence is stated in the
  integers, with the range given in the entry. Since the denominator of the generating function
  has constant term 1, the identity A(x) = N/D for A(x) = Sum_(n >= 0) a(n) x^n is stated as
  A * D = N in the formal power series ring over the integers.
* The closed form is stated for n > 0 (as in the entry), multiplied by 990, in the integers.
* Controls from the entry: the definition gives 1, 11, 111, 1110, 11101, 111010 for n = 0..5.
-/

namespace OMA.S_oeis_a266592

open PowerSeries

/-- Wolfram's code: the new cell is bit 4l + 2c + r of the rule number. -/
def eca (rule : ℕ) (l c r : Bool) : Bool := Nat.testBit rule (4 * l.toNat + 2 * c.toNat + r.toNat)

/-- Stage t of Rule 37 from a single ON cell at 0. -/
def state : ℕ → ℤ → Bool
  | 0, i => decide (i = 0)
  | t + 1, i => eca 37 (state t (i - 1)) (state t i) (state t (i + 1))

/-- A266592(n): the middle cells of stages 0..n read as base-10 digits, stage 0 first. -/
def a (n : ℕ) : ℕ :=
  ∑ t ∈ Finset.range (n + 1), if state t 0 then 10 ^ (n - t) else 0

/-- Barker's closed form, recurrence and generating function. -/
theorem main :
    (∀ n : ℕ, 0 < n → 990 * (a n : ℤ) = 45 * (-1) ^ n + 1099 * 10 ^ n - 55) ∧
    (∀ n : ℕ, 3 < n →
      (a n : ℤ) = 10 * a (n - 1) + a (n - 2) - 10 * a (n - 3)) ∧
    mk (fun n => (a n : ℤ)) * ((1 - X) * (1 + X) * (1 - 10 * X)) =
      (1 + X - X ^ 3 : PowerSeries ℤ) := by
  sorry

end OMA.S_oeis_a266592

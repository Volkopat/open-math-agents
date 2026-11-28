import Mathlib

/-!
# OEIS A267045: Barker's conjectures for the decimal middle column of Rule 91

Source: https://oeis.org/A267045 (Colin Barker, Jan 10 2016 and Apr 17 2019)

Entry A267045 (Robert Price, Jan 09 2016), offset 0: Decimal representation of the middle column of the Rule 91 elementary cellular automaton starting with a single ON (black) cell.
Formula section:
Conjectures from Colin Barker, Jan 10 2016 and Apr 17 2019: (Start)
a(n) = (2*(-1)^n+13*2^n-6)/12 for n>1.
a(n) = 2*a(n-1)+a(n-2)-2*a(n-3) for n>4. [Typo corrected by Karl V. Keller, Jr., Mar 16 2022]
G.f.: (1-x^2+x^4) / ((1-x)*(1+x)*(1-2*x)).
(End)

Formalization notes:
* Rule numbering: Wolfram's numbering of elementary cellular automata; the new value of cell i is
  bit 4l + 2c + r of the rule number, where l, c, r are the old values of cells i-1, i, i+1.
* Initial condition: at stage 0 cell 0 is ON and every other cell of Z is OFF; each stage applies
  the rule to every cell (Rule 91 maps 000 to ON and 111 to OFF), as
  CellularAutomaton[rule, {{1},0}, ...] does in the entry's program.
* Counting convention: as in the entry's program, the middle cells (cell 0) of stages 0..n are
  written as bits, stage 0 first, and read in base 2 (FromDigits in base 2 of the
  first n+1 middle cells).
* The statement is the conjunction of Barker's closed form, recurrence and generating function. The recurrence is stated in the
  integers, with the range given in the entry. Since the denominator of the generating function
  has constant term 1, the identity A(x) = N/D for A(x) = Sum_(n >= 0) a(n) x^n is stated as
  A * D = N in the formal power series ring over the integers.
* The closed form is stated for n > 1 (as in the entry), multiplied by 12, in the integers.
* Controls from the entry: the definition gives 1, 2, 4, 8, 17, 34 for n = 0..5.
-/

namespace OMA.S_oeis_a267045

open PowerSeries

/-- Wolfram's code: the new cell is bit 4l + 2c + r of the rule number. -/
def eca (rule : ℕ) (l c r : Bool) : Bool := Nat.testBit rule (4 * l.toNat + 2 * c.toNat + r.toNat)

/-- Stage t of Rule 91 from a single ON cell at 0. -/
def state : ℕ → ℤ → Bool
  | 0, i => decide (i = 0)
  | t + 1, i => eca 91 (state t (i - 1)) (state t i) (state t (i + 1))

/-- A267045(n): the middle cells of stages 0..n read as base-2 digits, stage 0 first. -/
def a (n : ℕ) : ℕ :=
  ∑ t ∈ Finset.range (n + 1), if state t 0 then 2 ^ (n - t) else 0

/-- Barker's closed form, recurrence and generating function. -/
theorem main :
    (∀ n : ℕ, 1 < n → 12 * (a n : ℤ) = 2 * (-1) ^ n + 13 * 2 ^ n - 6) ∧
    (∀ n : ℕ, 4 < n →
      (a n : ℤ) = 2 * a (n - 1) + a (n - 2) - 2 * a (n - 3)) ∧
    mk (fun n => (a n : ℤ)) * ((1 - X) * (1 + X) * (1 - 2 * X)) =
      (1 - X ^ 2 + X ^ 4 : PowerSeries ℤ) := by
  sorry

end OMA.S_oeis_a267045

import Mathlib

/-!
# OEIS A266984: Barker's conjectures for the decimal representation of Rule 81

Source: https://oeis.org/A266984 (Colin Barker, Jan 08 2016 and Apr 17 2019)

Entry A266984 (Robert Price, Jan 07 2016), offset 0: Decimal representation of the n-th iteration of the Rule 81 elementary cellular automaton starting with a single ON (black) cell.
Formula section:
Conjectures from Colin Barker, Jan 08 2016 and Apr 17 2019: (Start)
a(n) = ((-4)^n+(-1)^n-1)/2+4^n for n>0.
a(n) = 17*a(n-2)-16*a(n-4) for n>4.
G.f.: (1+2*x)*(1-x+9*x^2-4*x^3) / ((1-x)*(1+x)*(1-4*x)*(1+4*x)).
(End)

Formalization notes:
* Rule numbering: Wolfram's numbering of elementary cellular automata; the new value of cell i is
  bit 4l + 2c + r of the rule number, where l, c, r are the old values of cells i-1, i, i+1.
* Initial condition: at stage 0 cell 0 is ON and every other cell of Z is OFF; each stage applies
  the rule to every cell (Rule 81 maps 000 to ON and 111 to OFF), as
  CellularAutomaton[rule, {{1},0}, ...] does in the entry's program.
* Counting convention: a(n) writes the cells -n..n of stage n as bits, leftmost cell
  first, and reads them in base 2, as the entry's program does (Take the middle 2n+1 cells,
  FromDigits in base 2).
* The statement is the conjunction of Barker's closed form, recurrence and generating function. The recurrence is stated in the
  integers, with the range given in the entry. Since the denominator of the generating function
  has constant term 1, the identity A(x) = N/D for A(x) = Sum_(n >= 0) a(n) x^n is stated as
  A * D = N in the formal power series ring over the integers.
* The closed form is stated for n > 0 (as in the entry), multiplied by 2 to clear the denominator, in the integers.
* Controls from the entry: the definition gives 1, 1, 24, 31, 384, 511 for n = 0..5.
-/

namespace OMA.S_oeis_a266984

open PowerSeries

/-- Wolfram's code: the new cell is bit 4l + 2c + r of the rule number. -/
def eca (rule : ℕ) (l c r : Bool) : Bool := Nat.testBit rule (4 * l.toNat + 2 * c.toNat + r.toNat)

/-- Stage t of Rule 81 from a single ON cell at 0. -/
def state : ℕ → ℤ → Bool
  | 0, i => decide (i = 0)
  | t + 1, i => eca 81 (state t (i - 1)) (state t i) (state t (i + 1))

/-- A266984(n): the cells -n..n of stage n read as base-2 digits, leftmost first. -/
def a (n : ℕ) : ℕ :=
  ∑ k ∈ Finset.range (2 * n + 1), if state n ((k : ℤ) - (n : ℤ)) then 2 ^ (2 * n - k) else 0

/-- Barker's closed form, recurrence and generating function. -/
theorem main :
    (∀ n : ℕ, 0 < n → 2 * (a n : ℤ) = (-4) ^ n + (-1) ^ n - 1 + 2 * 4 ^ n) ∧
    (∀ n : ℕ, 4 < n →
      (a n : ℤ) = 17 * a (n - 2) - 16 * a (n - 4)) ∧
    mk (fun n => (a n : ℤ)) * ((1 - X) * (1 + X) * (1 - 4 * X) * (1 + 4 * X)) =
      ((1 + 2 * X) * (1 - X + 9 * X ^ 2 - 4 * X ^ 3) : PowerSeries ℤ) := by
  sorry

end OMA.S_oeis_a266984

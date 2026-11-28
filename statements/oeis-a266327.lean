import Mathlib

/-!
# OEIS A266327: Barker's conjectures for the binary representation of Rule 20

Source: https://oeis.org/A266327 (Colin Barker, Dec 28 2015 and Apr 18 2019)

Entry A266327 (Robert Price, Dec 27 2015), offset 0: Binary representation of the n-th iteration of the Rule 20 elementary cellular automaton starting with a single ON (black) cell.
Formula section:
Conjectures from Colin Barker, Dec 28 2015 and Apr 18 2019: (Start)
a(n) = 6-5*(-1)^n.
a(n) = a(n-2) for n>1.
G.f.: (1+11*x) / ((1-x)*(1+x)).
(End)

Formalization notes:
* Rule numbering: Wolfram's numbering of elementary cellular automata; the new value of cell i is
  bit 4l + 2c + r of the rule number, where l, c, r are the old values of cells i-1, i, i+1.
* Initial condition: at stage 0 cell 0 is ON and every other cell of Z is OFF; each stage applies
  the rule to every cell (Rule 20 maps 000 to OFF and 111 to OFF), as
  CellularAutomaton[rule, {{1},0}, ...] does in the entry's program.
* Counting convention: a(n) writes the cells -n..n of stage n as binary digits, leftmost cell
  first, and reads them in base 10, as the entry's program does (Take the middle 2n+1 cells,
  FromDigits with the default base 10).
* The statement is the conjunction of Barker's closed form, recurrence and generating function. The recurrence is stated in the
  integers, with the range given in the entry. Since the denominator of the generating function
  has constant term 1, the identity A(x) = N/D for A(x) = Sum_(n >= 0) a(n) x^n is stated as
  A * D = N in the formal power series ring over the integers.
* The closed form is stated for every n >= 0 (no range is stated) in the integers.
* Controls from the entry: the definition gives 1, 11, 1, 11, 1, 11 for n = 0..5.
-/

namespace OMA.S_oeis_a266327

open PowerSeries

/-- Wolfram's code: the new cell is bit 4l + 2c + r of the rule number. -/
def eca (rule : ℕ) (l c r : Bool) : Bool := Nat.testBit rule (4 * l.toNat + 2 * c.toNat + r.toNat)

/-- Stage t of Rule 20 from a single ON cell at 0. -/
def state : ℕ → ℤ → Bool
  | 0, i => decide (i = 0)
  | t + 1, i => eca 20 (state t (i - 1)) (state t i) (state t (i + 1))

/-- A266327(n): the cells -n..n of stage n read as base-10 digits, leftmost first. -/
def a (n : ℕ) : ℕ :=
  ∑ k ∈ Finset.range (2 * n + 1), if state n ((k : ℤ) - (n : ℤ)) then 10 ^ (2 * n - k) else 0

/-- Barker's closed form, recurrence and generating function. -/
theorem main :
    (∀ n : ℕ, 1 * (a n : ℤ) = 6 - 5 * (-1) ^ n) ∧
    (∀ n : ℕ, 1 < n →
      (a n : ℤ) = a (n - 2)) ∧
    mk (fun n => (a n : ℤ)) * ((1 - X) * (1 + X)) =
      (1 + 11 * X : PowerSeries ℤ) := by
  sorry

end OMA.S_oeis_a266327

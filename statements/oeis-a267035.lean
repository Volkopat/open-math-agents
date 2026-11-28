import Mathlib

/-!
# OEIS A267035: Barker's conjectures for the binary representation of Rule 85

Source: https://oeis.org/A267035 (Colin Barker, Jan 11 2016 and Apr 19 2019)

Entry A267035 (Robert Price, Jan 09 2016), offset 0: Binary representation of the n-th iteration of the Rule 85 elementary cellular automaton starting with a single ON (black) cell.
Formula section:
Conjectures from Colin Barker, Jan 11 2016 and Apr 19 2019: (Start)
a(n) = 10001*a(n-2)-10000*a(n-4) for n>3.
G.f.: (1+11*x-x^2+1100*x^3) / ((1-x)*(1+x)*(1-100*x)*(1+100*x)).
(End)

Formalization notes:
* Rule numbering: Wolfram's numbering of elementary cellular automata; the new value of cell i is
  bit 4l + 2c + r of the rule number, where l, c, r are the old values of cells i-1, i, i+1.
* Initial condition: at stage 0 cell 0 is ON and every other cell of Z is OFF; each stage applies
  the rule to every cell (Rule 85 maps 000 to ON and 111 to OFF), as
  CellularAutomaton[rule, {{1},0}, ...] does in the entry's program.
* Counting convention: a(n) writes the cells -n..n of stage n as binary digits, leftmost cell
  first, and reads them in base 10, as the entry's program does (Take the middle 2n+1 cells,
  FromDigits with the default base 10).
* The statement is the conjunction of Barker's recurrence and generating function. The recurrence is stated in the
  integers, with the range given in the entry. Since the denominator of the generating function
  has constant term 1, the identity A(x) = N/D for A(x) = Sum_(n >= 0) a(n) x^n is stated as
  A * D = N in the formal power series ring over the integers.
* Controls from the entry: the definition gives 1, 11, 10000, 111111, 100000000, 1111111111 for n = 0..5.
-/

namespace OMA.S_oeis_a267035

open PowerSeries

/-- Wolfram's code: the new cell is bit 4l + 2c + r of the rule number. -/
def eca (rule : ℕ) (l c r : Bool) : Bool := Nat.testBit rule (4 * l.toNat + 2 * c.toNat + r.toNat)

/-- Stage t of Rule 85 from a single ON cell at 0. -/
def state : ℕ → ℤ → Bool
  | 0, i => decide (i = 0)
  | t + 1, i => eca 85 (state t (i - 1)) (state t i) (state t (i + 1))

/-- A267035(n): the cells -n..n of stage n read as base-10 digits, leftmost first. -/
def a (n : ℕ) : ℕ :=
  ∑ k ∈ Finset.range (2 * n + 1), if state n ((k : ℤ) - (n : ℤ)) then 10 ^ (2 * n - k) else 0

/-- Barker's recurrence and generating function. -/
theorem main :
    (∀ n : ℕ, 3 < n →
      (a n : ℤ) = 10001 * a (n - 2) - 10000 * a (n - 4)) ∧
    mk (fun n => (a n : ℤ)) * ((1 - X) * (1 + X) * (1 - 100 * X) * (1 + 100 * X)) =
      (1 + 11 * X - X ^ 2 + 1100 * X ^ 3 : PowerSeries ℤ) := by
  sorry

end OMA.S_oeis_a267035

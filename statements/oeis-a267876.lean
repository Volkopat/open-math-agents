import Mathlib

/-!
# OEIS A267876: Barker's conjectures for the binary representation of Rule 233

Source: https://oeis.org/A267876 (Colin Barker, Jan 22 2016 and Apr 20 2019)

Entry A267876 (Robert Price, Jan 21 2016), offset 0: Binary representation of the n-th iteration of the Rule 233 elementary cellular automaton starting with a single ON (black) cell.
Formula section:
Conjectures from Colin Barker, Jan 22 2016 and Apr 20 2019: (Start)
a(n) = 101*a(n-1)-100*a(n-2) for n>3.
G.f.: (1-101*x+10201*x^2+89910*x^3-100000*x^5) / ((1-x)*(1-100*x)).
(End)

Formalization notes:
* Rule numbering: Wolfram's numbering of elementary cellular automata; the new value of cell i is
  bit 4l + 2c + r of the rule number, where l, c, r are the old values of cells i-1, i, i+1.
* Initial condition: at stage 0 cell 0 is ON and every other cell of Z is OFF; each stage applies
  the rule to every cell (Rule 233 maps 000 to ON and 111 to ON), as
  CellularAutomaton[rule, {{1},0}, ...] does in the entry's program.
* Counting convention: a(n) writes the cells -n..n of stage n as binary digits, leftmost cell
  first, and reads them in base 10, as the entry's program does (Take the middle 2n+1 cells,
  FromDigits with the default base 10).
* The statement is the conjunction of Barker's recurrence and generating function. The recurrence is stated in the
  integers, with the range given in the entry. Since the denominator of the generating function
  has constant term 1, the identity A(x) = N/D for A(x) = Sum_(n >= 0) a(n) x^n is stated as
  A * D = N in the formal power series ring over the integers.
* The recurrence as stated (for n > 3) fails at n = 5: a(5) = 11111111111, while
  101*a(4) - 100*a(3) = 11111211111. The generating function is consistent with the data;
  the recurrence it implies only holds from n = 6 on.
* Controls from the entry: the definition gives 1, 0, 10101, 1110111, 111111111, 11111111111 for n = 0..5.
-/

namespace OMA.S_oeis_a267876

open PowerSeries

/-- Wolfram's code: the new cell is bit 4l + 2c + r of the rule number. -/
def eca (rule : ℕ) (l c r : Bool) : Bool := Nat.testBit rule (4 * l.toNat + 2 * c.toNat + r.toNat)

/-- Stage t of Rule 233 from a single ON cell at 0. -/
def state : ℕ → ℤ → Bool
  | 0, i => decide (i = 0)
  | t + 1, i => eca 233 (state t (i - 1)) (state t i) (state t (i + 1))

/-- A267876(n): the cells -n..n of stage n read as base-10 digits, leftmost first. -/
def a (n : ℕ) : ℕ :=
  ∑ k ∈ Finset.range (2 * n + 1), if state n ((k : ℤ) - (n : ℤ)) then 10 ^ (2 * n - k) else 0

/-- Barker's recurrence and generating function. -/
theorem main :
    (∀ n : ℕ, 3 < n →
      (a n : ℤ) = 101 * a (n - 1) - 100 * a (n - 2)) ∧
    mk (fun n => (a n : ℤ)) * ((1 - X) * (1 - 100 * X)) =
      (1 - 101 * X + 10201 * X ^ 2 + 89910 * X ^ 3 - 100000 * X ^ 5 : PowerSeries ℤ) := by
  sorry

end OMA.S_oeis_a267876

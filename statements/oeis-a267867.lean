import Mathlib

/-!
# A267867: Binary representation of the n-th iteration of the Rule 231 elementary cellular automaton starting with a single ON (black) cell.

Source: https://oeis.org/A267867
Credit: @alkrssve

Text of the entry: OEIS Foundation and contributors, CC BY-SA 4.0. Read 2026-11-27.

The entry (Robert Price, Jan 21 2016, offset 0) lists, for each n, the middle 2n+1 cells of row n of Rule 231,
started from one ON cell on an all-OFF line, read as a number in base 10: the cells, each 0 or 1, are
written as decimal digits. Its program is CellularAutomaton[231, {{1},0}, ...], then Take the cells -n..n,
then FromDigits[...] with its default base 10. Its formula section has the conjectures stated here:

  Conjectures from Colin Barker, Jan 21 2016 and Apr 20 2019: (Start)
  a(n) = 101*a(n-1)-100*a(n-2) =A267850(n) for n>2.
  G.f.: (1+9*x+100*x^2) / ((1-x)*(1-100*x)).
  (End)

How it is stated:
* Rule numbering is Wolfram's: the new value of a cell is bit 4l + 2c + r of the rule number, where l, c, r
  are the old values of its left neighbour, the cell itself and its right neighbour.
* The rule acts on every cell of the integer line, so the OFF background changes as well
  (Rules 231 and 229 send three OFF cells to ON). This is what the entries' programs compute.
* digits R n reads the cells -n..n of row n of Rule R in base 10 with the leftmost cell most significant:
  cell n - k has weight 10^k for k = 0..2n. a is digits 231.
* The first conjecture is a chain a(n) = 101*a(n-1)-100*a(n-2) = A267850(n) for n > 2; both equalities are
  stated, in the integers because of the subtraction. A267850 is the entry with the same construction for
  Rule 229 (Binary representation of the n-th iteration of the Rule 229 elementary cellular automaton
  starting with a single ON (black) cell, same author, offset 0, same program with 229), so it is digits 229.
* The denominator of the generating function has constant term 1, so A(x) = N(x) / D(x) is stated as
  A * D = N, where A is the formal power series with coefficients a(n) over the integers.
* Check against the entries' data: these definitions give 1, 110, 11110, 1111110, 111111110 for a(0..4)
  and 1, 10, 11110, 1111110, 111111110 for A267850(0..4).
-/

namespace OMA.S_oeis_a267867

open PowerSeries

/-- Wolfram's numbering of elementary cellular automata: the new value of a cell is bit
`4l + 2c + r` of the rule number `R`, where `l`, `c`, `r` are the old values of the cell to its left,
the cell itself and the cell to its right. -/
def rule (R : ℕ) (l c r : Bool) : Bool := Nat.testBit R (4 * l.toNat + 2 * c.toNat + r.toNat)

/-- Row `n` of Rule `R` on the whole line, started from a single ON cell at position 0. -/
def row (R : ℕ) : ℕ → ℤ → Bool
  | 0, i => decide (i = 0)
  | n + 1, i => rule R (row R n (i - 1)) (row R n i) (row R n (i + 1))

/-- The cells `-n..n` of row `n` of Rule `R` read in base 10, leftmost cell first. -/
def digits (R n : ℕ) : ℕ := ∑ k ∈ Finset.range (2 * n + 1), if row R n ((n : ℤ) - k) then 10 ^ k else 0

/-- A267867(n): Rule 231. -/
def a (n : ℕ) : ℕ := digits 231 n

/-- A267850(n): the same construction for Rule 229. -/
def A267850 (n : ℕ) : ℕ := digits 229 n

theorem main :
    (∀ n : ℕ, 2 < n → (a n : ℤ) = 101 * a (n - 1) - 100 * a (n - 2) ∧
        (101 * a (n - 1) - 100 * a (n - 2) : ℤ) = A267850 n) ∧
    PowerSeries.mk (fun n => (a n : ℤ)) * ((1 - X) * (1 - 100 * X)) = 1 + 9 * X + 100 * X ^ 2 := by
  sorry

end OMA.S_oeis_a267867

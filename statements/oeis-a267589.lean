import Mathlib

/-!
# A267589: Decimal representation of the middle column of the Rule 169 elementary cellular automaton starting with a single ON (black) cell.

Source: https://oeis.org/A267589
Credit: @alkrssve

Text of the entry: OEIS Foundation and contributors, CC BY-SA 4.0. Read 2026-11-27.

The entry (Robert Price, Jan 18 2016, offset 0) lists, for each n, the cells of the middle column (position 0) in rows 0..n, row 0 first, read in base 2,
for Rule 169 started from one ON cell on an all-OFF line. Its program runs
CellularAutomaton[169, {{1},0}, ...], cuts row t to its cells -t..t, then keeps the middle cell of each row and applies FromDigits[..., 2] to the first n+1 of them.
Its formula section has the conjectures stated here:

  Conjectures from Colin Barker, Jan 18 2016 and Apr 20 2019: (Start)
  a(n) = 3*a(n-1)-2*a(n-2) for n>3.
  G.f.: (1-x+x^2-x^3+x^5) / ((1-x)*(1-2*x)).
  (End)

How it is stated:
* Rule numbering is Wolfram's: the new value of a cell is bit 4l + 2c + r of 169, where l, c, r
  are the old values of its left neighbour, the cell itself and its right neighbour.
* The rule acts on every cell of the integer line, so the background changes as well when the rule
  sends three OFF cells to ON (Rule 169 sends them to ON). This is what the entry's program computes.
* a n gives the middle cell of row t the weight 2^(n - t), for t = 0..n.
* main is the conjunction of the two conjectures, in the entry's order and with its ranges.
  The recurrence is stated in the integers because it subtracts.
  The denominator of the generating function has constant term 1, so A(x) = N(x) / D(x) is stated as
  A * D = N, where A is the formal power series with coefficients a(n) over the integers.
* Check against the entry's data: this definition gives 1, 2, 5, 10, 20, 41, 83 for n = 0..6.
-/

namespace OMA.S_oeis_a267589

open PowerSeries

/-- Wolfram's numbering of elementary cellular automata: the new value of a cell is bit
`4l + 2c + r` of the rule number, where `l`, `c`, `r` are the old values of the cell to its left,
the cell itself and the cell to its right. Here the rule number is 169. -/
def rule (l c r : Bool) : Bool := Nat.testBit 169 (4 * l.toNat + 2 * c.toNat + r.toNat)

/-- Row `n` of Rule 169 on the whole line, started from a single ON cell at position 0. -/
def row : ℕ → ℤ → Bool
  | 0, i => decide (i = 0)
  | n + 1, i => rule (row n (i - 1)) (row n i) (row n (i + 1))

/-- A267589(n): the middle cells of rows `0..n` read in base 2, row 0 most significant. -/
def a (n : ℕ) : ℕ := ∑ t ∈ Finset.range (n + 1), if row t 0 then 2 ^ (n - t) else 0

theorem main :
    (∀ n : ℕ, 3 < n → (a n : ℤ) = 3 * a (n - 1) - 2 * a (n - 2)) ∧
    PowerSeries.mk (fun n => (a n : ℤ)) * ((1 - X) * (1 - 2 * X)) = 1 - X + X ^ 2 - X ^ 3 + X ^ 5 := by
  sorry

end OMA.S_oeis_a267589

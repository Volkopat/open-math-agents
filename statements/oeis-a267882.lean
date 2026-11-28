import Mathlib

/-!
# A267882: Total number of ON (black) cells after n iterations of the Rule 233 elementary cellular
automaton starting with a single ON (black) cell

Source: https://oeis.org/A267882
Credit: @alkrssve

Text of the entry: OEIS Foundation and contributors, CC BY-SA 4.0. Read 2026-11-27.

The entry (Robert Price, Jan 21 2016, offset 0) lists, for each n, the total number of ON cells in
rows 0..n of Rule 233, started from one ON cell on an all-OFF line, where row t is cut to its middle
2t+1 cells. Its program is CellularAutomaton[233, {{1},0}, ...], then Take the cells -t..t of row t,
Total of each row, and the running total of these.
Its formula section has the conjectures stated here:

  Conjectures from Colin Barker, Jan 22 2016 and Apr 20 2019: (Start)
  a(n) = 3*a(n-1)-3*a(n-2)+a(n-3) for n>2.
  G.f.: (1-2*x+4*x^2-x^5) / (1-x)^3. (End)
  Conjectured e.g.f.: exp(x)*(x^2 + 3*x - 5) + x^2/2 + 3*x + 6. - Stefano Spezia, Sep 08 2025

How it is stated:
* Rule numbering is Wolfram's: the new value of a cell is bit 4l + 2c + r of 233, where l, c, r
  are the old values of its left neighbour, the cell itself and its right neighbour.
* The rule acts on every cell of the integer line, so the OFF background changes as well
  (Rule 233 sends three OFF cells to ON). This is what the entry's program computes.
* on t counts the ON cells among the cells -t..t of row t, and a n is the sum of on t for t = 0..n.
* main is the conjunction of the three conjectures, with the range of the entry. The recurrence is
  stated in the integers because it subtracts. The denominator of the generating function has
  constant term 1, so A(x) = N(x) / D(x) is stated as A * D = N, where A is the formal power series
  with coefficients a(n) over the integers. The exponential generating function is the formal power
  series over the rationals with coefficients a(n) / n!, and exp(x) is the formal power series
  PowerSeries.exp.
* Check against the entry's data: this definition gives 1, 1, 4, 10, 19, 30, 43 for n = 0..6.
-/

namespace OMA.S_oeis_a267882

open PowerSeries

/-- Wolfram's numbering of elementary cellular automata: the new value of a cell is bit
`4l + 2c + r` of the rule number, where `l`, `c`, `r` are the old values of the cell to its left,
the cell itself and the cell to its right. Here the rule number is 233. -/
def rule (l c r : Bool) : Bool := Nat.testBit 233 (4 * l.toNat + 2 * c.toNat + r.toNat)

/-- Row `n` of Rule 233 on the whole line, started from a single ON cell at position 0. -/
def row : ℕ → ℤ → Bool
  | 0, i => decide (i = 0)
  | n + 1, i => rule (row n (i - 1)) (row n i) (row n (i + 1))

/-- The number of ON cells among the cells `-t..t` of row `t`. -/
def on (t : ℕ) : ℕ := ∑ k ∈ Finset.range (2 * t + 1), if row t ((t : ℤ) - k) then 1 else 0

/-- A267882(n): the total number of ON cells in rows `0..n`. -/
def a (n : ℕ) : ℕ := ∑ t ∈ Finset.range (n + 1), on t

theorem main :
    (∀ n : ℕ, 2 < n → (a n : ℤ) = 3 * a (n - 1) - 3 * a (n - 2) + a (n - 3)) ∧
    PowerSeries.mk (fun n => (a n : ℤ)) * (1 - X) ^ 3 = 1 - 2 * X + 4 * X ^ 2 - X ^ 5 ∧
    PowerSeries.mk (fun n => (a n : ℚ) / (Nat.factorial n : ℚ)) =
      PowerSeries.exp ℚ * (X ^ 2 + 3 * X - 5) + C (1 / 2 : ℚ) * X ^ 2 + 3 * X + 6 := by
  sorry

end OMA.S_oeis_a267882

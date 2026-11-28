import Mathlib

/-!
# A265382: Total number of ON (black) cells after n iterations of the Rule 158 elementary cellular automaton starting with a single ON (black) cell.

Source: https://oeis.org/A265382
Credit: @alkrssve

Text of the entry: OEIS Foundation and contributors, CC BY-SA 4.0. Read 2026-11-27.

The entry (Robert Price, Dec 07 2015, offset 0) lists, for each n, the total number of ON cells in rows 0..n, where row t is cut to its middle 2t+1 cells,
for Rule 158 started from one ON cell on an all-OFF line. Its program runs
CellularAutomaton[158, {{1},0}, ...], cuts row t to its cells -t..t, then takes the cells -t..t of row t, the Total of each row, and the running total of these.
Its formula section has the conjectures stated here:

  Conjectures from Colin Barker, Dec 07 2015 and Apr 18 2019: (Start)
  a(n) = 1/16*(10*n^2+2*(-1)^n*n+34*n-3*(-1)^n+19).
  a(n) = 1/16*(10*n^2+36*n+16) for n even.
  a(n) = 1/16*(10*n^2+32*n+22) for n odd.
  a(n) = 2*a(n-1) - 2*a(n-2) - a(n-3) + a(n-4) for n>4.
  G.f.: (1+3*x+2*x^2-x^3) / ((1-x)^3*(1+x)^2).
  (End)

How it is stated:
* Rule numbering is Wolfram's: the new value of a cell is bit 4l + 2c + r of 158, where l, c, r
  are the old values of its left neighbour, the cell itself and its right neighbour.
* The rule acts on every cell of the integer line, so the background changes as well when the rule
  sends three OFF cells to ON (Rule 158 sends them to OFF). This is what the entry's program computes.
* on t counts the ON cells among the cells -t..t of row t, and a n is the sum of on t for t = 0..n.
* main is the conjunction of the five conjectures, in the entry's order and with its ranges.
  The three closed forms are stated in the rationals; the recurrence in the integers because it subtracts.
  The denominator of the generating function has constant term 1, so A(x) = N(x) / D(x) is stated as
  A * D = N, where A is the formal power series with coefficients a(n) over the integers.
* Check against the entry's data: this definition gives 1, 4, 8, 13, 20, 27, 37 for n = 0..6.
-/

namespace OMA.S_oeis_a265382

open PowerSeries

/-- Wolfram's numbering of elementary cellular automata: the new value of a cell is bit
`4l + 2c + r` of the rule number, where `l`, `c`, `r` are the old values of the cell to its left,
the cell itself and the cell to its right. Here the rule number is 158. -/
def rule (l c r : Bool) : Bool := Nat.testBit 158 (4 * l.toNat + 2 * c.toNat + r.toNat)

/-- Row `n` of Rule 158 on the whole line, started from a single ON cell at position 0. -/
def row : ℕ → ℤ → Bool
  | 0, i => decide (i = 0)
  | n + 1, i => rule (row n (i - 1)) (row n i) (row n (i + 1))

/-- The number of ON cells among the cells `-t..t` of row `t`. -/
def on (t : ℕ) : ℕ := ∑ k ∈ Finset.range (2 * t + 1), if row t ((t : ℤ) - k) then 1 else 0

/-- A265382(n): the total number of ON cells in rows `0..n`. -/
def a (n : ℕ) : ℕ := ∑ t ∈ Finset.range (n + 1), on t

theorem main :
    (∀ n : ℕ, (a n : ℚ) = 1 / 16 * (10 * (n : ℚ) ^ 2 + 2 * (-1) ^ n * n + 34 * n - 3 * (-1) ^ n + 19)) ∧
    (∀ n : ℕ, Even n → (a n : ℚ) = 1 / 16 * (10 * (n : ℚ) ^ 2 + 36 * n + 16)) ∧
    (∀ n : ℕ, Odd n → (a n : ℚ) = 1 / 16 * (10 * (n : ℚ) ^ 2 + 32 * n + 22)) ∧
    (∀ n : ℕ, 4 < n → (a n : ℤ) = 2 * a (n - 1) - 2 * a (n - 2) - a (n - 3) + a (n - 4)) ∧
    PowerSeries.mk (fun n => (a n : ℤ)) * ((1 - X) ^ 3 * (1 + X) ^ 2) = 1 + 3 * X + 2 * X ^ 2 - X ^ 3 := by
  sorry

end OMA.S_oeis_a265382

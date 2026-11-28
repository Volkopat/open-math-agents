import Mathlib

/-!
# A266794: Number of OFF (white) cells in the n-th iteration of the Rule 61 elementary cellular automaton starting with a single ON (black) cell.

Source: https://oeis.org/A266794
Credit: @alkrssve

Text of the entry: OEIS Foundation and contributors, CC BY-SA 4.0. Read 2026-11-27.

The entry (Robert Price, Jan 03 2016, offset 0) lists, for each n, the number of OFF cells among the middle 2n+1 cells of row n,
for Rule 61 started from one ON cell on an all-OFF line. Its program runs
CellularAutomaton[61, {{1},0}, ...], cuts row t to its cells -t..t, then takes the cells -n..n of row n and subtracts their Total from their Length.
Its formula section has the conjectures stated here:

  Conjectures from Colin Barker, Jan 04 2016 and Apr 17 2019: (Start)
  a(n) = n+(-1)^n*(n-4) for n>4.
  a(n) = 2*a(n-2)-a(n-4) for n>7.
  G.f.: x*(1+3*x-x^3+x^4+x^5-2*x^6+x^7) / ((1-x)^2*(1+x)^2).
  (End)

How it is stated:
* Rule numbering is Wolfram's: the new value of a cell is bit 4l + 2c + r of 61, where l, c, r
  are the old values of its left neighbour, the cell itself and its right neighbour.
* The rule acts on every cell of the integer line, so the background changes as well when the rule
  sends three OFF cells to ON (Rule 61 sends them to ON). This is what the entry's program computes.
* a n counts the OFF cells among the cells -n..n of row n.
* main is the conjunction of the three conjectures, in the entry's order and with its ranges.
  The closed form and the recurrence are stated in the integers because they subtract.
  The denominator of the generating function has constant term 1, so A(x) = N(x) / D(x) is stated as
  A * D = N, where A is the formal power series with coefficients a(n) over the integers.
* Check against the entry's data: this definition gives 0, 1, 3, 2, 5, 4, 8 for n = 0..6.
-/

namespace OMA.S_oeis_a266794

open PowerSeries

/-- Wolfram's numbering of elementary cellular automata: the new value of a cell is bit
`4l + 2c + r` of the rule number, where `l`, `c`, `r` are the old values of the cell to its left,
the cell itself and the cell to its right. Here the rule number is 61. -/
def rule (l c r : Bool) : Bool := Nat.testBit 61 (4 * l.toNat + 2 * c.toNat + r.toNat)

/-- Row `n` of Rule 61 on the whole line, started from a single ON cell at position 0. -/
def row : ℕ → ℤ → Bool
  | 0, i => decide (i = 0)
  | n + 1, i => rule (row n (i - 1)) (row n i) (row n (i + 1))

/-- A266794(n): the number of OFF cells among the cells `-n..n` of row `n`. -/
def a (n : ℕ) : ℕ := ∑ k ∈ Finset.range (2 * n + 1), if row n ((n : ℤ) - k) then 0 else 1

theorem main :
    (∀ n : ℕ, 4 < n → (a n : ℤ) = n + (-1) ^ n * ((n : ℤ) - 4)) ∧
    (∀ n : ℕ, 7 < n → (a n : ℤ) = 2 * a (n - 2) - a (n - 4)) ∧
    PowerSeries.mk (fun n => (a n : ℤ)) * ((1 - X) ^ 2 * (1 + X) ^ 2) =
      X * (1 + 3 * X - X ^ 3 + X ^ 4 + X ^ 5 - 2 * X ^ 6 + X ^ 7) := by
  sorry

end OMA.S_oeis_a266794

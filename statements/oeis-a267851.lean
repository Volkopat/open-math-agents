import Mathlib

/-!
# A267851: Decimal representation of the n-th iteration of the Rule 229 elementary cellular automaton starting with a single ON (black) cell.

Source: https://oeis.org/A267851
Credit: @alkrssve

Text of the entry: OEIS Foundation and contributors, CC BY-SA 4.0. Read 2026-11-27.

The entry (Robert Price, Jan 21 2016, offset 0) lists, for each n, the middle 2n+1 cells of row n of Rule 229,
started from one ON cell on an all-OFF line, read as a number in base 2: the cells are the binary digits of a(n).
Its program is CellularAutomaton[229, {{1},0}, ...], then Take the cells -n..n, then FromDigits[..., 2].
Its formula section has the conjectures stated here:

  Conjectures from Colin Barker, Jan 21 2016: (Start)
  a(n) = 5*a(n-1)-4*a(n-2) for n>3.
  G.f.: (1-3*x+24*x^2-16*x^3) / ((1-x)*(1-4*x)).
  (End)
  Conjecture: a(n) = 2*(4^n - 1) = A002446(n) for n>1. - Colin Barker, Nov 26 2016

How it is stated:
* Rule numbering is Wolfram's: the new value of a cell is bit 4l + 2c + r of 229, where l, c, r
  are the old values of its left neighbour, the cell itself and its right neighbour.
* The rule acts on every cell of the integer line, so the OFF background changes as well
  (Rule 229 sends three OFF cells to ON). This is what the entry's program computes.
* a n reads the cells -n..n of row n in base 2 with the leftmost cell most significant:
  cell n - k has weight 2^k for k = 0..2n.
* main is the conjunction of the conjectures above, with the ranges of the entry. The recurrence is
  stated in the integers because it subtracts. The denominator of the generating function has
  constant term 1, so A(x) = N(x) / D(x) is stated as A * D = N, where A is the formal power series
  with coefficients a(n) over the integers.
* The third conjecture names another entry. A002446 is defined by its own title,
  a(n) = 2^(2*n+1) - 2 (offset 0), and that formula is used here for A002446. Both equalities of
  the chain are stated, in the natural numbers (4^n - 1 and 2^(2n+1) - 2 never go below zero).
* Check against the entry's data: this definition gives 1, 2, 30, 126, 510 for n = 0..4.
-/
namespace OMA.S_oeis_a267851

open PowerSeries

/-- Wolfram's numbering of elementary cellular automata: the new value of a cell is bit
`4l + 2c + r` of the rule number, where `l`, `c`, `r` are the old values of the cell to its left,
the cell itself and the cell to its right. Here the rule number is 229. -/
def rule (l c r : Bool) : Bool := Nat.testBit 229 (4 * l.toNat + 2 * c.toNat + r.toNat)

/-- Row `n` of Rule 229 on the whole line, started from a single ON cell at position 0. -/
def row : ℕ → ℤ → Bool
  | 0, i => decide (i = 0)
  | n + 1, i => rule (row n (i - 1)) (row n i) (row n (i + 1))

/-- A267851(n): the cells `-n..n` of row `n` read in base 2, leftmost cell first. -/
def a (n : ℕ) : ℕ := ∑ k ∈ Finset.range (2 * n + 1), if row n ((n : ℤ) - k) then 2 ^ k else 0

/-- A002446(n) = 2^(2n+1) - 2: the title of that entry is this formula. -/
def A002446 (n : ℕ) : ℕ := 2 ^ (2 * n + 1) - 2

theorem main :
    (∀ n : ℕ, 3 < n → (a n : ℤ) = 5 * a (n - 1) - 4 * a (n - 2)) ∧
    PowerSeries.mk (fun n => (a n : ℤ)) * ((1 - X) * (1 - 4 * X)) = 1 - 3 * X + 24 * X ^ 2 - 16 * X ^ 3 ∧
    (∀ n : ℕ, 1 < n → a n = 2 * (4 ^ n - 1) ∧ 2 * (4 ^ n - 1) = A002446 n) := by
  sorry

end OMA.S_oeis_a267851

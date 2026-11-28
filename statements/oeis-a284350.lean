import Mathlib

/-!
# A284350: Decimal representation of the x-axis, from the origin to the right edge, of the n-th stage of growth of the two-dimensional cellular automaton defined by 'Rule 873', based on the 5-celled von Neumann neighborhood.

Source: https://oeis.org/A284350
Credit: @clementtrecourt

The conjectures listed in the entry, all stated below as one conjunction:
* a(n) = 2*a(n-1) + a(n-8) - 2*a(n-9) for n > 23.
* G.f.: (-32768*x^23 + 8192*x^22 - 6144*x^21 + 2560*x^20 + 768*x^19 + 256*x^18 + 32608*x^15 - 8144*x^14 + 6128*x^13 - 2544*x^12 - 768*x^11 - 132*x^10 - 20*x^9 - 11*x^8 + 158*x^7 - 46*x^6 + 26*x^5 - 10*x^4 - 2*x^3 + 6*x^2 - 2*x + 1)/(2*x^9 - x^8 - 2*x + 1).

Conventions (as in Wolfram's numbering and the OEIS program): the automaton runs on the integer lattice ℤ², starting from one ON cell at (0, 0) on an all-OFF background, and the rule is applied to every cell, including the background, at each step (the OEIS program runs on a torus large enough that wrap-around never reaches the counted square). The rule and the initial state are invariant under the symmetries of the square, so every state is too; the half-axis or half-diagonal named in the entry is read along the cells listed below.
Offset 0: a(n) is the number whose binary digits, from most to least significant, are the states after n steps of the cells (0, 0), (1, 0), ..., (n, 0).
The definition below reproduces every term listed in the OEIS entry. Each formula was checked against the automaton for every n up to 100.
-/

namespace OMA.S_oeis_a284350

/-- `cell code t i j` is the value of the cell at `(i, j)` after `t` steps of the two-dimensional
outer totalistic cellular automaton with Wolfram code `code` on the 5-celled von Neumann
neighbourhood, starting from a single ON cell at `(0, 0)` on an all-OFF background: the new value
of a cell is bit number `c + 2 * s` of `code`, where `c` is its old value and `s` is the number of
ON cells among its four neighbours. -/
def cell (code : ℕ) : ℕ → ℤ → ℤ → Bool
  | 0 => fun i j => decide (i = 0 ∧ j = 0)
  | t + 1 => fun i j => code.testBit ((cell code t i j).toNat + 2 * ((cell code t (i + 1) j).toNat +
      (cell code t (i - 1) j).toNat + (cell code t i (j + 1)).toNat + (cell code t i (j - 1)).toNat))

/-- The number of ON cells in the square `[-t, t] × [-t, t]` after `t` steps. -/
def onCount (code t : ℕ) : ℕ :=
  ∑ i ∈ Finset.range (2 * t + 1), ∑ j ∈ Finset.range (2 * t + 1),
    if cell code t ((i : ℤ) - t) ((j : ℤ) - t) then 1 else 0

/-- A284350(n): the number whose binary digits, from most to least significant, are the states after n steps of the cells (0, 0), (1, 0), ..., (n, 0). -/
def a (n : ℕ) : ℤ :=
  ∑ k ∈ Finset.range (n + 1), if cell 873 n k 0 then (2 : ℤ) ^ (n - k) else 0

open PowerSeries in
theorem main :
    (∀ n : ℕ, 24 ≤ n → (a n : ℚ) = 2 * a (n - 1) + a (n - 8) - 2 * a (n - 9)) ∧
    (PowerSeries.mk (fun n => (a n : ℚ)) * (2 * X ^ 9 - X ^ 8 - 2 * X + 1 : PowerSeries ℚ) = -32768 * X ^ 23 + 8192 * X ^ 22 - 6144 * X ^ 21 + 2560 * X ^ 20 + 768 * X ^ 19 + 256 * X ^ 18 + 32608 * X ^ 15 - 8144 * X ^ 14 + 6128 * X ^ 13 - 2544 * X ^ 12 - 768 * X ^ 11 - 132 * X ^ 10 - 20 * X ^ 9 - 11 * X ^ 8 + 158 * X ^ 7 - 46 * X ^ 6 + 26 * X ^ 5 - 10 * X ^ 4 - 2 * X ^ 3 + 6 * X ^ 2 - 2 * X + 1) := by
  sorry

end OMA.S_oeis_a284350

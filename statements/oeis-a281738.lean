import Mathlib

/-!
# A281738: Decimal representation of the x-axis, from the origin to the right edge, of the n-th stage of growth of the two-dimensional cellular automaton defined by 'Rule 390', based on the 5-celled von Neumann neighborhood.

Source: https://oeis.org/A281738
Credit: @clementtrecourt

The conjectures listed in the entry, all stated below as one conjunction:
* a(n) = a(n-2) for n > 25.
* G.f.: (12582912*x^25 + 4194304*x^24 - 10485760*x^23 - 3145728*x^22 - 1572864*x^21 - 786432*x^20 - 393216*x^19 - 196608*x^18 - 98304*x^17 - 49152*x^16 - 24576*x^15 - 12288*x^14 - 6144*x^13 - 3072*x^12 - 1600*x^11 - 960*x^10 - 256*x^9 - 160*x^7 - 48*x^6 - 32*x^5 - 16*x^4 - 4*x^3 - 3*x - 1)/(x^2 - 1).

Conventions (as in Wolfram's numbering and the OEIS program): the automaton runs on the integer lattice ℤ², starting from one ON cell at (0, 0) on an all-OFF background, and the rule is applied to every cell, including the background, at each step (the OEIS program runs on a torus large enough that wrap-around never reaches the counted square). The rule and the initial state are invariant under the symmetries of the square, so every state is too; the half-axis or half-diagonal named in the entry is read along the cells listed below.
Offset 0: a(n) is the number whose binary digits, from most to least significant, are the states after n steps of the cells (0, 0), (1, 0), ..., (n, 0).
The definition below reproduces every term listed in the OEIS entry. Each formula was checked against the automaton for every n up to 100.
-/

namespace OMA.S_oeis_a281738

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

/-- A281738(n): the number whose binary digits, from most to least significant, are the states after n steps of the cells (0, 0), (1, 0), ..., (n, 0). -/
def a (n : ℕ) : ℤ :=
  ∑ k ∈ Finset.range (n + 1), if cell 390 n k 0 then (2 : ℤ) ^ (n - k) else 0

open PowerSeries in
theorem main :
    (∀ n : ℕ, 26 ≤ n → (a n : ℚ) = a (n - 2)) ∧
    (PowerSeries.mk (fun n => (a n : ℚ)) * (X ^ 2 - 1 : PowerSeries ℚ) = 12582912 * X ^ 25 + 4194304 * X ^ 24 - 10485760 * X ^ 23 - 3145728 * X ^ 22 - 1572864 * X ^ 21 - 786432 * X ^ 20 - 393216 * X ^ 19 - 196608 * X ^ 18 - 98304 * X ^ 17 - 49152 * X ^ 16 - 24576 * X ^ 15 - 12288 * X ^ 14 - 6144 * X ^ 13 - 3072 * X ^ 12 - 1600 * X ^ 11 - 960 * X ^ 10 - 256 * X ^ 9 - 160 * X ^ 7 - 48 * X ^ 6 - 32 * X ^ 5 - 16 * X ^ 4 - 4 * X ^ 3 - 3 * X - 1) := by
  sorry

end OMA.S_oeis_a281738

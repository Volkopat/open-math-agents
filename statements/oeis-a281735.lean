import Mathlib

/-!
# A281735: Binary representation of the x-axis, from the left edge to the origin, of the n-th stage of growth of the two-dimensional cellular automaton defined by 'Rule 390', based on the 5-celled von Neumann neighborhood.

Source: https://oeis.org/A281735
Credit: @clementtrecourt

The conjectures listed in the entry, all stated below as one conjunction:
* a(n) = 100*a(n-2) for n > 25.
* G.f.: (1100*x^25 + 100*x^24 + 89*x^23 + 99*x^22 + 99*x^21 + 99*x^20 + 99*x^19 + 99*x^18 + 99*x^17 + 99*x^16 + 99*x^15 + 99*x^14 + 99*x^13 + 99*x^12 + 110999*x^11 + 9999*x^10 - 10*x^9 + 89*x^7 + 99*x^6 - x^5 - x^4 - 10*x^3 - 11*x - 1)/(100*x^2 - 1).

Conventions (as in Wolfram's numbering and the OEIS program): the automaton runs on the integer lattice ℤ², starting from one ON cell at (0, 0) on an all-OFF background, and the rule is applied to every cell, including the background, at each step (the OEIS program runs on a torus large enough that wrap-around never reaches the counted square). The rule and the initial state are invariant under the symmetries of the square, so every state is too; the half-axis or half-diagonal named in the entry is read along the cells listed below.
Offset 0: a(n) is the number whose decimal digits (each 0 or 1), from most to least significant, are the states after n steps of the cells (-n, 0), (-n + 1, 0), ..., (0, 0).
The definition below reproduces every term listed in the OEIS entry. Each formula was checked against the automaton for every n up to 100.
-/

namespace OMA.S_oeis_a281735

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

/-- A281735(n): the number whose decimal digits (each 0 or 1), from most to least significant, are the states after n steps of the cells (-n, 0), (-n + 1, 0), ..., (0, 0). -/
def a (n : ℕ) : ℤ :=
  ∑ k ∈ Finset.range (n + 1), if cell 390 n ((k : ℤ) - n) 0 then (10 : ℤ) ^ (n - k) else 0

open PowerSeries in
theorem main :
    (∀ n : ℕ, 26 ≤ n → (a n : ℚ) = 100 * a (n - 2)) ∧
    (PowerSeries.mk (fun n => (a n : ℚ)) * (100 * X ^ 2 - 1 : PowerSeries ℚ) = 1100 * X ^ 25 + 100 * X ^ 24 + 89 * X ^ 23 + 99 * X ^ 22 + 99 * X ^ 21 + 99 * X ^ 20 + 99 * X ^ 19 + 99 * X ^ 18 + 99 * X ^ 17 + 99 * X ^ 16 + 99 * X ^ 15 + 99 * X ^ 14 + 99 * X ^ 13 + 99 * X ^ 12 + 110999 * X ^ 11 + 9999 * X ^ 10 - 10 * X ^ 9 + 89 * X ^ 7 + 99 * X ^ 6 - X ^ 5 - X ^ 4 - 10 * X ^ 3 - 11 * X - 1) := by
  sorry

end OMA.S_oeis_a281735

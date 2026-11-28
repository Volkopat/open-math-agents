import Mathlib

/-!
# A283405: Binary representation of the x-axis, from the origin to the right edge, of the n-th stage of growth of the two-dimensional cellular automaton defined by 'Rule 637', based on the 5-celled von Neumann neighborhood.

Source: https://oeis.org/A283405
Credit: @clementtrecourt

The conjectures listed in the entry, all stated below as one conjunction:
* a(n) = 10*a(n-1) + a(n-2) - 10*a(n-3) for n > 33.
* G.f.: (-11000000000000000000000000000000*x^33 + 100000000000000000000000000000*x^32 + 11000000000000000000000000000000*x^31 - 100000000000000000000000000000*x^30 + 88900000000*x^13 + 1010000000*x^12 - 89990000000*x^11 - 1000000000*x^10 + 1090000000*x^9 - 10000000*x^8 + 100000*x^7 - 90000*x^5 - 1000*x^4 + 1100*x^3 - 10*x^2 - 9*x + 1)/((x - 1)*(x + 1)*(10*x - 1)).

Conventions (as in Wolfram's numbering and the OEIS program): the automaton runs on the integer lattice ℤ², starting from one ON cell at (0, 0) on an all-OFF background, and the rule is applied to every cell, including the background, at each step (the OEIS program runs on a torus large enough that wrap-around never reaches the counted square). The rule and the initial state are invariant under the symmetries of the square, so every state is too; the half-axis or half-diagonal named in the entry is read along the cells listed below.
Offset 0: a(n) is the number whose decimal digits (each 0 or 1), from most to least significant, are the states after n steps of the cells (0, 0), (1, 0), ..., (n, 0).
The definition below reproduces every term listed in the OEIS entry. Each formula was checked against the automaton for every n up to 100.
-/

namespace OMA.S_oeis_a283405

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

/-- A283405(n): the number whose decimal digits (each 0 or 1), from most to least significant, are the states after n steps of the cells (0, 0), (1, 0), ..., (n, 0). -/
def a (n : ℕ) : ℤ :=
  ∑ k ∈ Finset.range (n + 1), if cell 637 n k 0 then (10 : ℤ) ^ (n - k) else 0

open PowerSeries in
theorem main :
    (∀ n : ℕ, 34 ≤ n → (a n : ℚ) = 10 * a (n - 1) + a (n - 2) - 10 * a (n - 3)) ∧
    (PowerSeries.mk (fun n => (a n : ℚ)) * ((X - 1) * (X + 1) * (10 * X - 1) : PowerSeries ℚ) = -11000000000000000000000000000000 * X ^ 33 + 100000000000000000000000000000 * X ^ 32 + 11000000000000000000000000000000 * X ^ 31 - 100000000000000000000000000000 * X ^ 30 + 88900000000 * X ^ 13 + 1010000000 * X ^ 12 - 89990000000 * X ^ 11 - 1000000000 * X ^ 10 + 1090000000 * X ^ 9 - 10000000 * X ^ 8 + 100000 * X ^ 7 - 90000 * X ^ 5 - 1000 * X ^ 4 + 1100 * X ^ 3 - 10 * X ^ 2 - 9 * X + 1) := by
  sorry

end OMA.S_oeis_a283405

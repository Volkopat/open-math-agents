import Mathlib

/-!
# A281749: Binary representation of the x-axis, from the origin to the right edge, of the n-th stage of growth of the two-dimensional cellular automaton defined by 'Rule 395', based on the 5-celled von Neumann neighborhood.

Source: https://oeis.org/A281749
Credit: @clementtrecourt

The conjectures listed in the entry, all stated below as one conjunction:
* a(n) = - 10*a(n-1) + 1000*a(n-3) + 10000*a(n-4) + a(n-8) + 10*a(n-9) - 1000*a(n-11) - 10000*a(n-12) for n > 19.
* G.f.: (-10000000000*x^19 - 1000000000*x^18 - 100000000*x^17 + 1000000*x^15 - 90000*x^12 + 991000*x^11 + 1100*x^9 - 99790*x^8 - 8880*x^7 + 211*x^6 + 1120*x^5 - 9789*x^4 + 120*x^3 + 211*x^2 + 20*x + 1)/(10000*x^12 + 1000*x^11 - 10*x^9 - x^8 - 10000*x^4 - 1000*x^3 + 10*x + 1).

Conventions (as in Wolfram's numbering and the OEIS program): the automaton runs on the integer lattice ℤ², starting from one ON cell at (0, 0) on an all-OFF background, and the rule is applied to every cell, including the background, at each step (the OEIS program runs on a torus large enough that wrap-around never reaches the counted square). The rule and the initial state are invariant under the symmetries of the square, so every state is too; the half-axis or half-diagonal named in the entry is read along the cells listed below.
Offset 0: a(n) is the number whose decimal digits (each 0 or 1), from most to least significant, are the states after n steps of the cells (0, 0), (1, 0), ..., (n, 0).
The definition below reproduces every term listed in the OEIS entry. Each formula was checked against the automaton for every n up to 100.
-/

namespace OMA.S_oeis_a281749

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

/-- A281749(n): the number whose decimal digits (each 0 or 1), from most to least significant, are the states after n steps of the cells (0, 0), (1, 0), ..., (n, 0). -/
def a (n : ℕ) : ℤ :=
  ∑ k ∈ Finset.range (n + 1), if cell 395 n k 0 then (10 : ℤ) ^ (n - k) else 0

open PowerSeries in
theorem main :
    (∀ n : ℕ, 20 ≤ n → (a n : ℚ) = -10 * a (n - 1) + 1000 * a (n - 3) + 10000 * a (n - 4) + a (n - 8) + 10 * a (n - 9) - 1000 * a (n - 11) - 10000 * a (n - 12)) ∧
    (PowerSeries.mk (fun n => (a n : ℚ)) * (10000 * X ^ 12 + 1000 * X ^ 11 - 10 * X ^ 9 - X ^ 8 - 10000 * X ^ 4 - 1000 * X ^ 3 + 10 * X + 1 : PowerSeries ℚ) = -10000000000 * X ^ 19 - 1000000000 * X ^ 18 - 100000000 * X ^ 17 + 1000000 * X ^ 15 - 90000 * X ^ 12 + 991000 * X ^ 11 + 1100 * X ^ 9 - 99790 * X ^ 8 - 8880 * X ^ 7 + 211 * X ^ 6 + 1120 * X ^ 5 - 9789 * X ^ 4 + 120 * X ^ 3 + 211 * X ^ 2 + 20 * X + 1) := by
  sorry

end OMA.S_oeis_a281749

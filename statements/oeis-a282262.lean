import Mathlib

/-!
# A282262: Binary representation of the x-axis, from the origin to the right edge, of the n-th stage of growth of the two-dimensional cellular automaton defined by 'Rule 446', based on the 5-celled von Neumann neighborhood.

Source: https://oeis.org/A282262
Credit: @clementtrecourt

The conjectures listed in the entry, all stated below as one conjunction:
* a(n) = 100*a(n-2) + a(n-8) - 100*a(n-10) for n > 17.
* G.f.: (1000000000000*x^17 - 10000000*x^15 + 1100000000*x^14 - 110101000000*x^13 - 910100000*x^12 + 1111100000*x^11 + 10100000*x^10 - 11111000*x^9 - 101090*x^8 + 11100011*x^7 + 99911*x^6 - 110989*x^5 - 1089*x^4 + 11*x^3 - 89*x^2 + 11*x + 1)/(100*x^10 - x^8 - 100*x^2 + 1).

Conventions (as in Wolfram's numbering and the OEIS program): the automaton runs on the integer lattice ℤ², starting from one ON cell at (0, 0) on an all-OFF background, and the rule is applied to every cell, including the background, at each step (the OEIS program runs on a torus large enough that wrap-around never reaches the counted square). The rule and the initial state are invariant under the symmetries of the square, so every state is too; the half-axis or half-diagonal named in the entry is read along the cells listed below.
Offset 0: a(n) is the number whose decimal digits (each 0 or 1), from most to least significant, are the states after n steps of the cells (0, 0), (1, 0), ..., (n, 0).
The definition below reproduces every term listed in the OEIS entry. Each formula was checked against the automaton for every n up to 100.
-/

namespace OMA.S_oeis_a282262

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

/-- A282262(n): the number whose decimal digits (each 0 or 1), from most to least significant, are the states after n steps of the cells (0, 0), (1, 0), ..., (n, 0). -/
def a (n : ℕ) : ℤ :=
  ∑ k ∈ Finset.range (n + 1), if cell 446 n k 0 then (10 : ℤ) ^ (n - k) else 0

open PowerSeries in
theorem main :
    (∀ n : ℕ, 18 ≤ n → (a n : ℚ) = 100 * a (n - 2) + a (n - 8) - 100 * a (n - 10)) ∧
    (PowerSeries.mk (fun n => (a n : ℚ)) * (100 * X ^ 10 - X ^ 8 - 100 * X ^ 2 + 1 : PowerSeries ℚ) = 1000000000000 * X ^ 17 - 10000000 * X ^ 15 + 1100000000 * X ^ 14 - 110101000000 * X ^ 13 - 910100000 * X ^ 12 + 1111100000 * X ^ 11 + 10100000 * X ^ 10 - 11111000 * X ^ 9 - 101090 * X ^ 8 + 11100011 * X ^ 7 + 99911 * X ^ 6 - 110989 * X ^ 5 - 1089 * X ^ 4 + 11 * X ^ 3 - 89 * X ^ 2 + 11 * X + 1) := by
  sorry

end OMA.S_oeis_a282262

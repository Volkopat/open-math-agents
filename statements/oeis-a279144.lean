import Mathlib

/-!
# A279144: Decimal representation of the x-axis, from the origin to the right edge, of the n-th stage of growth of the two-dimensional cellular automaton defined by 'Rule 137', based on the 5-celled von Neumann neighborhood.

Source: https://oeis.org/A279144
Credit: @clementtrecourt

The conjectures listed in the entry, all stated below as one conjunction:
* a(n) = - 2*a(n-1) + 8*a(n-3) + 16*a(n-4) + a(n-8) + 2*a(n-9) - 8*a(n-11) - 16*a(n-12) for n > 15.
* G.f.: (-14336*x^15 - 2048*x^14 + 224*x^13 + 32*x^12 + 224*x^9 + 36*x^8 + 2*x^7 + 5*x^6 + 2*x^5 + 5*x^4 + 2*x^3 + 5*x^2 + 2*x + 1)/(16*x^12 + 8*x^11 - 2*x^9 - x^8 - 16*x^4 - 8*x^3 + 2*x + 1).

Conventions (as in Wolfram's numbering and the OEIS program): the automaton runs on the integer lattice ℤ², starting from one ON cell at (0, 0) on an all-OFF background, and the rule is applied to every cell, including the background, at each step (the OEIS program runs on a torus large enough that wrap-around never reaches the counted square). The rule and the initial state are invariant under the symmetries of the square, so every state is too; the half-axis or half-diagonal named in the entry is read along the cells listed below.
Offset 0: a(n) is the number whose binary digits, from most to least significant, are the states after n steps of the cells (0, 0), (1, 0), ..., (n, 0).
The definition below reproduces every term listed in the OEIS entry. Each formula was checked against the automaton for every n up to 100.
-/

namespace OMA.S_oeis_a279144

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

/-- A279144(n): the number whose binary digits, from most to least significant, are the states after n steps of the cells (0, 0), (1, 0), ..., (n, 0). -/
def a (n : ℕ) : ℤ :=
  ∑ k ∈ Finset.range (n + 1), if cell 137 n k 0 then (2 : ℤ) ^ (n - k) else 0

open PowerSeries in
theorem main :
    (∀ n : ℕ, 16 ≤ n → (a n : ℚ) = -2 * a (n - 1) + 8 * a (n - 3) + 16 * a (n - 4) + a (n - 8) + 2 * a (n - 9) - 8 * a (n - 11) - 16 * a (n - 12)) ∧
    (PowerSeries.mk (fun n => (a n : ℚ)) * (16 * X ^ 12 + 8 * X ^ 11 - 2 * X ^ 9 - X ^ 8 - 16 * X ^ 4 - 8 * X ^ 3 + 2 * X + 1 : PowerSeries ℚ) = -14336 * X ^ 15 - 2048 * X ^ 14 + 224 * X ^ 13 + 32 * X ^ 12 + 224 * X ^ 9 + 36 * X ^ 8 + 2 * X ^ 7 + 5 * X ^ 6 + 2 * X ^ 5 + 5 * X ^ 4 + 2 * X ^ 3 + 5 * X ^ 2 + 2 * X + 1) := by
  sorry

end OMA.S_oeis_a279144

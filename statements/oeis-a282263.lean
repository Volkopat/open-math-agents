import Mathlib

/-!
# A282263: Decimal representation of the x-axis, from the left edge to the origin, of the n-th stage of growth of the two-dimensional cellular automaton defined by 'Rule 446', based on the 5-celled von Neumann neighborhood.

Source: https://oeis.org/A282263
Credit: @clementtrecourt

The conjectures listed in the entry, all stated below as one conjunction:
* a(n) = a(n-2) + 256*a(n-8) - 256*a(n-10) for n > 17.
* G.f.: (32*x^17 - 256*x^15 + 96*x^14 - 172*x^13 - 152*x^12 + 124*x^11 + 40*x^10 - 124*x^9 + 24*x^8 + 199*x^7 + 82*x^6 + 41*x^5 + 18*x^4 + 12*x^3 + 5*x^2 + 3*x + 1)/(256*x^10 - 256*x^8 - x^2 + 1).

Conventions (as in Wolfram's numbering and the OEIS program): the automaton runs on the integer lattice ℤ², starting from one ON cell at (0, 0) on an all-OFF background, and the rule is applied to every cell, including the background, at each step (the OEIS program runs on a torus large enough that wrap-around never reaches the counted square). The rule and the initial state are invariant under the symmetries of the square, so every state is too; the half-axis or half-diagonal named in the entry is read along the cells listed below.
Offset 0: a(n) is the number whose binary digits, from most to least significant, are the states after n steps of the cells (-n, 0), (-n + 1, 0), ..., (0, 0).
The definition below reproduces every term listed in the OEIS entry. Each formula was checked against the automaton for every n up to 100.
-/

namespace OMA.S_oeis_a282263

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

/-- A282263(n): the number whose binary digits, from most to least significant, are the states after n steps of the cells (-n, 0), (-n + 1, 0), ..., (0, 0). -/
def a (n : ℕ) : ℤ :=
  ∑ k ∈ Finset.range (n + 1), if cell 446 n ((k : ℤ) - n) 0 then (2 : ℤ) ^ (n - k) else 0

open PowerSeries in
theorem main :
    (∀ n : ℕ, 18 ≤ n → (a n : ℚ) = a (n - 2) + 256 * a (n - 8) - 256 * a (n - 10)) ∧
    (PowerSeries.mk (fun n => (a n : ℚ)) * (256 * X ^ 10 - 256 * X ^ 8 - X ^ 2 + 1 : PowerSeries ℚ) = 32 * X ^ 17 - 256 * X ^ 15 + 96 * X ^ 14 - 172 * X ^ 13 - 152 * X ^ 12 + 124 * X ^ 11 + 40 * X ^ 10 - 124 * X ^ 9 + 24 * X ^ 8 + 199 * X ^ 7 + 82 * X ^ 6 + 41 * X ^ 5 + 18 * X ^ 4 + 12 * X ^ 3 + 5 * X ^ 2 + 3 * X + 1) := by
  sorry

end OMA.S_oeis_a282263

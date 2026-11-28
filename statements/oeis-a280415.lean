import Mathlib

/-!
# A280415: Decimal representation of the x-axis, from the left edge to the origin, of the n-th stage of growth of the two-dimensional cellular automaton defined by 'Rule 262', based on the 5-celled von Neumann neighborhood.

Source: https://oeis.org/A280415
Credit: @clementtrecourt

The conjectures listed in the entry, all stated below as one conjunction:
* a(n) = 4*a(n-2) for n > 31.
* G.f.: (12*x^31 + 4*x^30 + x^29 + 3*x^28 + 3*x^27 + 3*x^26 + 3*x^25 + 3*x^24 + 3*x^23 + 3*x^22 + 3*x^21 + 3*x^20 + 3*x^19 + 3*x^18 + 3*x^17 + 3*x^16 + 3*x^15 + 3*x^14 + 3*x^13 + 3*x^12 + 55*x^11 + 15*x^10 - 2*x^9 + x^7 + 3*x^6 - x^5 - x^4 - 2*x^3 - 3*x - 1)/(4*x^2 - 1).

Conventions (as in Wolfram's numbering and the OEIS program): the automaton runs on the integer lattice ℤ², starting from one ON cell at (0, 0) on an all-OFF background, and the rule is applied to every cell, including the background, at each step (the OEIS program runs on a torus large enough that wrap-around never reaches the counted square). The rule and the initial state are invariant under the symmetries of the square, so every state is too; the half-axis or half-diagonal named in the entry is read along the cells listed below.
Offset 0: a(n) is the number whose binary digits, from most to least significant, are the states after n steps of the cells (-n, 0), (-n + 1, 0), ..., (0, 0).
The definition below reproduces every term listed in the OEIS entry. Each formula was checked against the automaton for every n up to 100.
-/

namespace OMA.S_oeis_a280415

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

/-- A280415(n): the number whose binary digits, from most to least significant, are the states after n steps of the cells (-n, 0), (-n + 1, 0), ..., (0, 0). -/
def a (n : ℕ) : ℤ :=
  ∑ k ∈ Finset.range (n + 1), if cell 262 n ((k : ℤ) - n) 0 then (2 : ℤ) ^ (n - k) else 0

open PowerSeries in
theorem main :
    (∀ n : ℕ, 32 ≤ n → (a n : ℚ) = 4 * a (n - 2)) ∧
    (PowerSeries.mk (fun n => (a n : ℚ)) * (4 * X ^ 2 - 1 : PowerSeries ℚ) = 12 * X ^ 31 + 4 * X ^ 30 + X ^ 29 + 3 * X ^ 28 + 3 * X ^ 27 + 3 * X ^ 26 + 3 * X ^ 25 + 3 * X ^ 24 + 3 * X ^ 23 + 3 * X ^ 22 + 3 * X ^ 21 + 3 * X ^ 20 + 3 * X ^ 19 + 3 * X ^ 18 + 3 * X ^ 17 + 3 * X ^ 16 + 3 * X ^ 15 + 3 * X ^ 14 + 3 * X ^ 13 + 3 * X ^ 12 + 55 * X ^ 11 + 15 * X ^ 10 - 2 * X ^ 9 + X ^ 7 + 3 * X ^ 6 - X ^ 5 - X ^ 4 - 2 * X ^ 3 - 3 * X - 1) := by
  sorry

end OMA.S_oeis_a280415

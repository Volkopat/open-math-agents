import Mathlib

/-!
# A281284: Decimal representation of the x-axis, from the origin to the right edge, of the n-th stage of growth of the two-dimensional cellular automaton defined by 'Rule 350', based on the 5-celled von Neumann neighborhood.

Source: https://oeis.org/A281284
Credit: @clementtrecourt

The conjectures listed in the entry, all stated below as one conjunction:
* a(n) = 17*a(n-4) - 16*a(n-8) for n > 23.
* G.f.: (49152*x^23 + 40960*x^22 - 32768*x^21 - 12288*x^20 - 61440*x^19 - 32768*x^18 + 32768*x^17 + 14080*x^16 - 2816*x^15 - 2048*x^14 - 1536*x^12 + 768*x^11 + 512*x^10 + 128*x^9 - 320*x^8 + 16*x^7 + 8*x^6 - 40*x^5 + 10*x^4 + 11*x^3 + 3*x^2 + 3*x + 1)/(16*x^8 - 17*x^4 + 1).

Conventions (as in Wolfram's numbering and the OEIS program): the automaton runs on the integer lattice ℤ², starting from one ON cell at (0, 0) on an all-OFF background, and the rule is applied to every cell, including the background, at each step (the OEIS program runs on a torus large enough that wrap-around never reaches the counted square). The rule and the initial state are invariant under the symmetries of the square, so every state is too; the half-axis or half-diagonal named in the entry is read along the cells listed below.
Offset 0: a(n) is the number whose binary digits, from most to least significant, are the states after n steps of the cells (0, 0), (1, 0), ..., (n, 0).
The definition below reproduces every term listed in the OEIS entry. Each formula was checked against the automaton for every n up to 100.
-/

namespace OMA.S_oeis_a281284

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

/-- A281284(n): the number whose binary digits, from most to least significant, are the states after n steps of the cells (0, 0), (1, 0), ..., (n, 0). -/
def a (n : ℕ) : ℤ :=
  ∑ k ∈ Finset.range (n + 1), if cell 350 n k 0 then (2 : ℤ) ^ (n - k) else 0

open PowerSeries in
theorem main :
    (∀ n : ℕ, 24 ≤ n → (a n : ℚ) = 17 * a (n - 4) - 16 * a (n - 8)) ∧
    (PowerSeries.mk (fun n => (a n : ℚ)) * (16 * X ^ 8 - 17 * X ^ 4 + 1 : PowerSeries ℚ) = 49152 * X ^ 23 + 40960 * X ^ 22 - 32768 * X ^ 21 - 12288 * X ^ 20 - 61440 * X ^ 19 - 32768 * X ^ 18 + 32768 * X ^ 17 + 14080 * X ^ 16 - 2816 * X ^ 15 - 2048 * X ^ 14 - 1536 * X ^ 12 + 768 * X ^ 11 + 512 * X ^ 10 + 128 * X ^ 9 - 320 * X ^ 8 + 16 * X ^ 7 + 8 * X ^ 6 - 40 * X ^ 5 + 10 * X ^ 4 + 11 * X ^ 3 + 3 * X ^ 2 + 3 * X + 1) := by
  sorry

end OMA.S_oeis_a281284

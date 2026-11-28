import Mathlib

/-!
# A281742: Decimal representation of the x-axis, from the origin to the right edge, of the n-th stage of growth of the two-dimensional cellular automaton defined by 'Rule 393', based on the 5-celled von Neumann neighborhood.

Source: https://oeis.org/A281742
Credit: @clementtrecourt

The conjectures listed in the entry, all stated below as one conjunction:
* a(n) = 4*a(n-2) + a(n-8) - 4*a(n-10) for n > 23.
* G.f.: (57344*x^23 - 69632*x^22 + 6144*x^21 + 5120*x^20 - 11776*x^19 + 3840*x^18 + 2816*x^17 - 1280*x^16 - 640*x^15 + 320*x^14 + 160*x^13 - 80*x^12 - 880*x^11 + 320*x^10 + 160*x^9 - 80*x^8 + 16*x^7 + x^6 + x^4 + x^2 + 1)/(4*x^10 - x^8 - 4*x^2 + 1).

Conventions (as in Wolfram's numbering and the OEIS program): the automaton runs on the integer lattice ℤ², starting from one ON cell at (0, 0) on an all-OFF background, and the rule is applied to every cell, including the background, at each step (the OEIS program runs on a torus large enough that wrap-around never reaches the counted square). The rule and the initial state are invariant under the symmetries of the square, so every state is too; the half-axis or half-diagonal named in the entry is read along the cells listed below.
Offset 0: a(n) is the number whose binary digits, from most to least significant, are the states after n steps of the cells (0, 0), (1, 0), ..., (n, 0).
The definition below reproduces every term listed in the OEIS entry. Each formula was checked against the automaton for every n up to 100.
-/

namespace OMA.S_oeis_a281742

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

/-- A281742(n): the number whose binary digits, from most to least significant, are the states after n steps of the cells (0, 0), (1, 0), ..., (n, 0). -/
def a (n : ℕ) : ℤ :=
  ∑ k ∈ Finset.range (n + 1), if cell 393 n k 0 then (2 : ℤ) ^ (n - k) else 0

open PowerSeries in
theorem main :
    (∀ n : ℕ, 24 ≤ n → (a n : ℚ) = 4 * a (n - 2) + a (n - 8) - 4 * a (n - 10)) ∧
    (PowerSeries.mk (fun n => (a n : ℚ)) * (4 * X ^ 10 - X ^ 8 - 4 * X ^ 2 + 1 : PowerSeries ℚ) = 57344 * X ^ 23 - 69632 * X ^ 22 + 6144 * X ^ 21 + 5120 * X ^ 20 - 11776 * X ^ 19 + 3840 * X ^ 18 + 2816 * X ^ 17 - 1280 * X ^ 16 - 640 * X ^ 15 + 320 * X ^ 14 + 160 * X ^ 13 - 80 * X ^ 12 - 880 * X ^ 11 + 320 * X ^ 10 + 160 * X ^ 9 - 80 * X ^ 8 + 16 * X ^ 7 + X ^ 6 + X ^ 4 + X ^ 2 + 1) := by
  sorry

end OMA.S_oeis_a281742

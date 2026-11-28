import Mathlib

/-!
# A284027: Decimal representation of the x-axis, from the origin to the right edge, of the n-th stage of growth of the two-dimensional cellular automaton defined by 'Rule 782', based on the 5-celled von Neumann neighborhood.

Source: https://oeis.org/A284027
Credit: @clementtrecourt

The conjectures listed in the entry, all stated below as one conjunction:
* a(n) = 2*a(n-1) - 4*a(n-2) + 8*a(n-3) + a(n-8) - 2*a(n-9) + 4*a(n-10) - 8*a(n-11) for n > 32.
* G.f.: (1048576*x^32 + 1310720*x^30 + 262144*x^28 + 327680*x^27 - 65536*x^26 - 49152*x^25 - 1118208*x^24 - 20480*x^23 - 1324032*x^22 - 5120*x^21 - 259072*x^20 - 327680*x^19 + 65280*x^18 + 48384*x^17 + 3840*x^16 + 19456*x^15 - 3328*x^14 - 256*x^13 - 256*x^12 - 976*x^11 - 64*x^10 - 252*x^9 + 64*x^8 + 49*x^7 + 5*x^6 + 5*x^5 + x^4 + x^3 + 5*x^2 + x + 1)/((x - 1)*(x + 1)*(2*x - 1)*(x^2 + 1)*(4*x^2 + 1)*(x^4 + 1)).

Conventions (as in Wolfram's numbering and the OEIS program): the automaton runs on the integer lattice ℤ², starting from one ON cell at (0, 0) on an all-OFF background, and the rule is applied to every cell, including the background, at each step (the OEIS program runs on a torus large enough that wrap-around never reaches the counted square). The rule and the initial state are invariant under the symmetries of the square, so every state is too; the half-axis or half-diagonal named in the entry is read along the cells listed below.
Offset 0: a(n) is the number whose binary digits, from most to least significant, are the states after n steps of the cells (0, 0), (1, 0), ..., (n, 0).
The definition below reproduces every term listed in the OEIS entry. Each formula was checked against the automaton for every n up to 100.
-/

namespace OMA.S_oeis_a284027

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

/-- A284027(n): the number whose binary digits, from most to least significant, are the states after n steps of the cells (0, 0), (1, 0), ..., (n, 0). -/
def a (n : ℕ) : ℤ :=
  ∑ k ∈ Finset.range (n + 1), if cell 782 n k 0 then (2 : ℤ) ^ (n - k) else 0

open PowerSeries in
theorem main :
    (∀ n : ℕ, 33 ≤ n → (a n : ℚ) = 2 * a (n - 1) - 4 * a (n - 2) + 8 * a (n - 3) + a (n - 8) - 2 * a (n - 9) + 4 * a (n - 10) - 8 * a (n - 11)) ∧
    (PowerSeries.mk (fun n => (a n : ℚ)) * ((X - 1) * (X + 1) * (2 * X - 1) * (X ^ 2 + 1) * (4 * X ^ 2 + 1) * (X ^ 4 + 1) : PowerSeries ℚ) = 1048576 * X ^ 32 + 1310720 * X ^ 30 + 262144 * X ^ 28 + 327680 * X ^ 27 - 65536 * X ^ 26 - 49152 * X ^ 25 - 1118208 * X ^ 24 - 20480 * X ^ 23 - 1324032 * X ^ 22 - 5120 * X ^ 21 - 259072 * X ^ 20 - 327680 * X ^ 19 + 65280 * X ^ 18 + 48384 * X ^ 17 + 3840 * X ^ 16 + 19456 * X ^ 15 - 3328 * X ^ 14 - 256 * X ^ 13 - 256 * X ^ 12 - 976 * X ^ 11 - 64 * X ^ 10 - 252 * X ^ 9 + 64 * X ^ 8 + 49 * X ^ 7 + 5 * X ^ 6 + 5 * X ^ 5 + X ^ 4 + X ^ 3 + 5 * X ^ 2 + X + 1) := by
  sorry

end OMA.S_oeis_a284027

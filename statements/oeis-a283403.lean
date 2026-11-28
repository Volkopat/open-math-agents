import Mathlib

/-!
# A283403: Decimal representation of the x-axis, from the origin to the right edge, of the n-th stage of growth of the two-dimensional cellular automaton defined by 'Rule 633', based on the 5-celled von Neumann neighborhood.

Source: https://oeis.org/A283403
Credit: @clementtrecourt

The conjectures listed in the entry, all stated below as one conjunction:
* a(n) = 2*a(n-1) + a(n-2) - 2*a(n-3) for n > 26.
* G.f.: (-25165824*x^26 + 4194304*x^25 + 25165824*x^24 - 4194304*x^23 + 128*x^12 + 320*x^11 - 448*x^10 - 256*x^9 + 320*x^8 - 64*x^7 + 16*x^6 - 8*x^4 - 2*x^3 + 5*x^2 - 2*x + 1)/((x - 1)*(x + 1)*(2*x - 1)).

Conventions (as in Wolfram's numbering and the OEIS program): the automaton runs on the integer lattice ℤ², starting from one ON cell at (0, 0) on an all-OFF background, and the rule is applied to every cell, including the background, at each step (the OEIS program runs on a torus large enough that wrap-around never reaches the counted square). The rule and the initial state are invariant under the symmetries of the square, so every state is too; the half-axis or half-diagonal named in the entry is read along the cells listed below.
Offset 0: a(n) is the number whose binary digits, from most to least significant, are the states after n steps of the cells (0, 0), (1, 0), ..., (n, 0).
The definition below reproduces every term listed in the OEIS entry. Each formula was checked against the automaton for every n up to 100.
-/

namespace OMA.S_oeis_a283403

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

/-- A283403(n): the number whose binary digits, from most to least significant, are the states after n steps of the cells (0, 0), (1, 0), ..., (n, 0). -/
def a (n : ℕ) : ℤ :=
  ∑ k ∈ Finset.range (n + 1), if cell 633 n k 0 then (2 : ℤ) ^ (n - k) else 0

open PowerSeries in
theorem main :
    (∀ n : ℕ, 27 ≤ n → (a n : ℚ) = 2 * a (n - 1) + a (n - 2) - 2 * a (n - 3)) ∧
    (PowerSeries.mk (fun n => (a n : ℚ)) * ((X - 1) * (X + 1) * (2 * X - 1) : PowerSeries ℚ) = -25165824 * X ^ 26 + 4194304 * X ^ 25 + 25165824 * X ^ 24 - 4194304 * X ^ 23 + 128 * X ^ 12 + 320 * X ^ 11 - 448 * X ^ 10 - 256 * X ^ 9 + 320 * X ^ 8 - 64 * X ^ 7 + 16 * X ^ 6 - 8 * X ^ 4 - 2 * X ^ 3 + 5 * X ^ 2 - 2 * X + 1) := by
  sorry

end OMA.S_oeis_a283403

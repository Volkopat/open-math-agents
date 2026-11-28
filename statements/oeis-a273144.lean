import Mathlib

/-!
# A273144: Number of active (ON, black) cells in n-th stage of growth of two-dimensional cellular automaton defined by 'Rule 597', based on the 5-celled von Neumann neighborhood.

Source: https://oeis.org/A273144
Credit: @clementtrecourt

The conjectures listed in the entry, all stated below as one conjunction:
* a(n) = 2*a(n-2)-2*a(n-6)+a(n-8) for n>7.
* G.f.: (1+8*x+18*x^2+25*x^3+17*x^4+22*x^5+4*x^6+x^7) / ((1-x)^3*(1+x)^3*(1+x^2)).

Conventions (as in Wolfram's numbering and the OEIS program): the automaton runs on the integer lattice ℤ², starting from one ON cell at (0, 0) on an all-OFF background, and the rule is applied to every cell, including the background, at each step (the OEIS program runs on a torus large enough that wrap-around never reaches the counted square).
Offset 0: a(n) is the number of ON cells in the square [-n, n] x [-n, n] after n steps.
The definition below reproduces every term listed in the OEIS entry. Each formula was checked against the automaton for every n up to 100.
-/

namespace OMA.S_oeis_a273144

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

/-- A273144(n): the number of ON cells in the square [-n, n] x [-n, n] after n steps. -/
def a (n : ℕ) : ℤ :=
  (onCount 597 n : ℤ)

open PowerSeries in
theorem main :
    (∀ n : ℕ, 8 ≤ n → (a n : ℚ) = 2 * a (n - 2) - 2 * a (n - 6) + a (n - 8)) ∧
    (PowerSeries.mk (fun n => (a n : ℚ)) * ((1 - X) ^ 3 * (1 + X) ^ 3 * (1 + X ^ 2) : PowerSeries ℚ) = 1 + 8 * X + 18 * X ^ 2 + 25 * X ^ 3 + 17 * X ^ 4 + 22 * X ^ 5 + 4 * X ^ 6 + X ^ 7) := by
  sorry

end OMA.S_oeis_a273144

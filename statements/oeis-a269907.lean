import Mathlib

/-!
# A269907: Number of active (ON, black) cells at stage 2^n-1 of the two-dimensional cellular automaton defined by 'Rule 1', based on the 5-celled von Neumann neighborhood.

Source: https://oeis.org/A269907
Credit: @clementtrecourt

The conjectures listed in the entry, all stated below as one conjunction:
* a(n) = 4*(4^n-2^n-1) for n>0.
* a(n) = 7*a(n-1)-14*a(n-2)+8*a(n-3) for n>3.
* G.f.: (1-3*x+30*x^2-40*x^3) / ((1-x)*(1-2*x)*(1-4*x)).

Conventions (as in Wolfram's numbering and the OEIS program): the automaton runs on the integer lattice ℤ², starting from one ON cell at (0, 0) on an all-OFF background, and the rule is applied to every cell, including the background, at each step (the OEIS program runs on a torus large enough that wrap-around never reaches the counted square).
Offset 0: a(n) is the number of ON cells in the square [-(2^n-1), 2^n-1]^2 after 2^n - 1 steps.
The definition below reproduces every term listed in the OEIS entry. Each formula was checked against the automaton for every n up to 9.
-/

namespace OMA.S_oeis_a269907

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

/-- A269907(n): the number of ON cells in the square [-(2^n-1), 2^n-1]^2 after 2^n - 1 steps. -/
def a (n : ℕ) : ℤ :=
  (onCount 1 (2 ^ n - 1) : ℤ)

open PowerSeries in
theorem main :
    (∀ n : ℕ, 1 ≤ n → (a n : ℚ) = 4 * ((4 : ℚ) ^ n - (2 : ℚ) ^ n - 1)) ∧
    (∀ n : ℕ, 4 ≤ n → (a n : ℚ) = 7 * a (n - 1) - 14 * a (n - 2) + 8 * a (n - 3)) ∧
    (PowerSeries.mk (fun n => (a n : ℚ)) * ((1 - X) * (1 - 2 * X) * (1 - 4 * X) : PowerSeries ℚ) = 1 - 3 * X + 30 * X ^ 2 - 40 * X ^ 3) := by
  sorry

end OMA.S_oeis_a269907

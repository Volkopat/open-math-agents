import Mathlib

/-!
# A273769: First differences of number of active (ON, black) cells in n-th stage of growth of two-dimensional cellular automaton defined by 'Rule 913', based on the 5-celled von Neumann neighborhood.

Source: https://oeis.org/A273769
Credit: @clementtrecourt

The conjectures listed in the entry, all stated below as one conjunction:
* a(n) = 8*(1+n) for n>3.
* a(n) = 2*a(n-1)-a(n-2) for n>5.
* G.f.: (3+7*x+8*x^2-16*x^3+5*x^4+x^5) / (1-x)^2.

Conventions (as in Wolfram's numbering and the OEIS program): the automaton runs on the integer lattice ℤ², starting from one ON cell at (0, 0) on an all-OFF background, and the rule is applied to every cell, including the background, at each step (the OEIS program runs on a torus large enough that wrap-around never reaches the counted square).
Offset 0: a(n) is c(n+1) - c(n), where c(t) is the number of ON cells in the square [-t, t] x [-t, t] after t steps.
The definition below reproduces every term listed in the OEIS entry. Each formula was checked against the automaton for every n up to 100.
-/

namespace OMA.S_oeis_a273769

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

/-- A273769(n): c(n+1) - c(n), where c(t) is the number of ON cells in the square [-t, t] x [-t, t] after t steps. -/
def a (n : ℕ) : ℤ :=
  (onCount 913 (n + 1) : ℤ) - onCount 913 n

open PowerSeries in
theorem main :
    (∀ n : ℕ, 4 ≤ n → (a n : ℚ) = 8 * (1 + (n : ℚ))) ∧
    (∀ n : ℕ, 6 ≤ n → (a n : ℚ) = 2 * a (n - 1) - a (n - 2)) ∧
    (PowerSeries.mk (fun n => (a n : ℚ)) * ((1 - X) ^ 2 : PowerSeries ℚ) = 3 + 7 * X + 8 * X ^ 2 - 16 * X ^ 3 + 5 * X ^ 4 + X ^ 5) := by
  sorry

end OMA.S_oeis_a273769

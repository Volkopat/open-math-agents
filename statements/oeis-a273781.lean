import Mathlib

/-!
# A273781: Partial sums of the number of active (ON, black) cells in n-th stage of growth of two-dimensional cellular automaton defined by 'Rule 929', based on the 5-celled von Neumann neighborhood.

Source: https://oeis.org/A273781
Credit: @clementtrecourt

The conjectures listed in the entry, all stated below as one conjunction:
* a(n) = (n-1)*(4*n^2+16*n+27)/3 for n>2.
* a(n) = 4*a(n-1)-6*a(n-2)+4*a(n-3)-a(n-4) for n>6.
* G.f.: (1+x+12*x^2-4*x^3-4*x^4+x^5+x^6) / (1-x)^4.

Conventions (as in Wolfram's numbering and the OEIS program): the automaton runs on the integer lattice ℤ², starting from one ON cell at (0, 0) on an all-OFF background, and the rule is applied to every cell, including the background, at each step (the OEIS program runs on a torus large enough that wrap-around never reaches the counted square).
Offset 0: a(n) is the sum over 0 <= k <= n of the number of ON cells in the square [-k, k] x [-k, k] after k steps.
The definition below reproduces every term listed in the OEIS entry. Each formula was checked against the automaton for every n up to 100.
-/

namespace OMA.S_oeis_a273781

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

/-- A273781(n): the sum over 0 <= k <= n of the number of ON cells in the square [-k, k] x [-k, k] after k steps. -/
def a (n : ℕ) : ℤ :=
  ∑ k ∈ Finset.range (n + 1), (onCount 929 k : ℤ)

open PowerSeries in
theorem main :
    (∀ n : ℕ, 3 ≤ n → (a n : ℚ) = ((n : ℚ) - 1) * (4 * (n : ℚ) ^ 2 + 16 * (n : ℚ) + 27) / 3) ∧
    (∀ n : ℕ, 7 ≤ n → (a n : ℚ) = 4 * a (n - 1) - 6 * a (n - 2) + 4 * a (n - 3) - a (n - 4)) ∧
    (PowerSeries.mk (fun n => (a n : ℚ)) * ((1 - X) ^ 4 : PowerSeries ℚ) = 1 + X + 12 * X ^ 2 - 4 * X ^ 3 - 4 * X ^ 4 + X ^ 5 + X ^ 6) := by
  sorry

end OMA.S_oeis_a273781

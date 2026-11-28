import Mathlib

/-!
# A271052: Partial sums of the number of active (ON, black) cells in n-th stage of growth of two-dimensional cellular automaton defined by 'Rule 253', based on the 5-celled von Neumann neighborhood.

Source: https://oeis.org/A271052
Credit: @clementtrecourt

The conjectures listed in the entry, all stated below as one conjunction:
* G.f.: (1 + 8*x + x^2 + 20*x^3 + 4*x^4 + 8*x^5 - 15*x^6 - 4*x^7 + 9*x^8) / ((1 - x)^4*(1 + x)^3).
* a(n) = (8*n^3 + 12*n^2 + 46*n - 48) / 12 for n>1 and even.
* a(n) = (8*n^3 + 36*n^2 + 94*n - 138) / 12 for n>1 and odd.
* a(n) = a(n-1) + 3*a(n-2) - 3*a(n-3) - 3*a(n-4) + 3*a(n-5) + a(n-6) - a(n-7) for n>8.

Conventions (as in Wolfram's numbering and the OEIS program): the automaton runs on the integer lattice ℤ², starting from one ON cell at (0, 0) on an all-OFF background, and the rule is applied to every cell, including the background, at each step (the OEIS program runs on a torus large enough that wrap-around never reaches the counted square).
Offset 0: a(n) is the sum over 0 <= k <= n of the number of ON cells in the square [-k, k] x [-k, k] after k steps.
The definition below reproduces every term listed in the OEIS entry. Each formula was checked against the automaton for every n up to 100.
-/

namespace OMA.S_oeis_a271052

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

/-- A271052(n): the sum over 0 <= k <= n of the number of ON cells in the square [-k, k] x [-k, k] after k steps. -/
def a (n : ℕ) : ℤ :=
  ∑ k ∈ Finset.range (n + 1), (onCount 253 k : ℤ)

open PowerSeries in
theorem main :
    (PowerSeries.mk (fun n => (a n : ℚ)) * ((1 - X) ^ 4 * (1 + X) ^ 3 : PowerSeries ℚ) = 1 + 8 * X + X ^ 2 + 20 * X ^ 3 + 4 * X ^ 4 + 8 * X ^ 5 - 15 * X ^ 6 - 4 * X ^ 7 + 9 * X ^ 8) ∧
    (∀ n : ℕ, 2 ≤ n → Even n → (a n : ℚ) = (8 * (n : ℚ) ^ 3 + 12 * (n : ℚ) ^ 2 + 46 * (n : ℚ) - 48) / 12) ∧
    (∀ n : ℕ, 2 ≤ n → Odd n → (a n : ℚ) = (8 * (n : ℚ) ^ 3 + 36 * (n : ℚ) ^ 2 + 94 * (n : ℚ) - 138) / 12) ∧
    (∀ n : ℕ, 9 ≤ n → (a n : ℚ) = a (n - 1) + 3 * a (n - 2) - 3 * a (n - 3) - 3 * a (n - 4) + 3 * a (n - 5) + a (n - 6) - a (n - 7)) := by
  sorry

end OMA.S_oeis_a271052

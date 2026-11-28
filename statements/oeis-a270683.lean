import Mathlib

/-!
# A270683: Partial sums of the number of active (ON, black) cells in n-th stage of growth of two-dimensional cellular automaton defined by 'Rule 190', based on the 5-celled von Neumann neighborhood.

Source: https://oeis.org/A270683
Credit: @clementtrecourt

The conjectures listed in the entry, all stated below as one conjunction:
* a(n) = (9+3*(-1)^n+7*n-3*(-1)^n*n+18*n^2+2*n^3)/6 for n>0.
* a(n) = (n^3+9*n^2+2*n+6)/3 for n>0 and even.
* a(n) = (n^3+9*n^2+5*n+3)/3 for n odd.
* a(n) = 2*a(n-1)+a(n-2)-4*a(n-3)+a(n-4)+2*a(n-5)-a(n-6) for n>6.
* G.f.: (1+4*x+5*x^2+4*x^3-5*x^4-x^6) / ((1-x)^4*(1+x)^2).

Conventions (as in Wolfram's numbering and the OEIS program): the automaton runs on the integer lattice ℤ², starting from one ON cell at (0, 0) on an all-OFF background, and the rule is applied to every cell, including the background, at each step (the OEIS program runs on a torus large enough that wrap-around never reaches the counted square).
Offset 0: a(n) is the sum over 0 <= k <= n of the number of ON cells in the square [-k, k] x [-k, k] after k steps.
The definition below reproduces every term listed in the OEIS entry. Each formula was checked against the automaton for every n up to 100.
-/

namespace OMA.S_oeis_a270683

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

/-- A270683(n): the sum over 0 <= k <= n of the number of ON cells in the square [-k, k] x [-k, k] after k steps. -/
def a (n : ℕ) : ℤ :=
  ∑ k ∈ Finset.range (n + 1), (onCount 190 k : ℤ)

open PowerSeries in
theorem main :
    (∀ n : ℕ, 1 ≤ n → (a n : ℚ) = (9 + 3 * (-1 : ℚ) ^ n + 7 * (n : ℚ) - 3 * (-1 : ℚ) ^ n * (n : ℚ) + 18 * (n : ℚ) ^ 2 + 2 * (n : ℚ) ^ 3) / 6) ∧
    (∀ n : ℕ, 1 ≤ n → Even n → (a n : ℚ) = ((n : ℚ) ^ 3 + 9 * (n : ℚ) ^ 2 + 2 * (n : ℚ) + 6) / 3) ∧
    (∀ n : ℕ, Odd n → (a n : ℚ) = ((n : ℚ) ^ 3 + 9 * (n : ℚ) ^ 2 + 5 * (n : ℚ) + 3) / 3) ∧
    (∀ n : ℕ, 7 ≤ n → (a n : ℚ) = 2 * a (n - 1) + a (n - 2) - 4 * a (n - 3) + a (n - 4) + 2 * a (n - 5) - a (n - 6)) ∧
    (PowerSeries.mk (fun n => (a n : ℚ)) * ((1 - X) ^ 4 * (1 + X) ^ 2 : PowerSeries ℚ) = 1 + 4 * X + 5 * X ^ 2 + 4 * X ^ 3 - 5 * X ^ 4 - X ^ 6) := by
  sorry

end OMA.S_oeis_a270683

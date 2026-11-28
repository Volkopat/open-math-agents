import Mathlib

/-!
# A273419: Partial sums of the number of active (ON, black) cells in n-th stage of growth of two-dimensional cellular automaton defined by 'Rule 705', based on the 5-celled von Neumann neighborhood.

Source: https://oeis.org/A273419
Credit: @clementtrecourt

The conjectures listed in the entry, all stated below as one conjunction:
* a(n) = (111-3*(-1)^n-58*n+48*n^2+16*n^3)/12 for n>1.
* a(n) = (8*n^3+24*n^2-29*n+54)/6 for n>1 and even.
* a(n) = (8*n^3+24*n^2-29*n+57)/6 for n>1 and odd.
* a(n) = 3*a(n-1)-2*a(n-2)-2*a(n-3)+3*a(n-4)-a(n-5) for n>6.
* G.f.: (1+2*x+13*x^2+x^3-3*x^4+7*x^5-5*x^6) / ((1-x)^4*(1+x)).

Conventions (as in Wolfram's numbering and the OEIS program): the automaton runs on the integer lattice ℤ², starting from one ON cell at (0, 0) on an all-OFF background, and the rule is applied to every cell, including the background, at each step (the OEIS program runs on a torus large enough that wrap-around never reaches the counted square).
Offset 0: a(n) is the sum over 0 <= k <= n of the number of ON cells in the square [-k, k] x [-k, k] after k steps.
The definition below reproduces every term listed in the OEIS entry. Each formula was checked against the automaton for every n up to 100.
-/

namespace OMA.S_oeis_a273419

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

/-- A273419(n): the sum over 0 <= k <= n of the number of ON cells in the square [-k, k] x [-k, k] after k steps. -/
def a (n : ℕ) : ℤ :=
  ∑ k ∈ Finset.range (n + 1), (onCount 705 k : ℤ)

open PowerSeries in
theorem main :
    (∀ n : ℕ, 2 ≤ n → (a n : ℚ) = (111 - 3 * (-1 : ℚ) ^ n - 58 * (n : ℚ) + 48 * (n : ℚ) ^ 2 + 16 * (n : ℚ) ^ 3) / 12) ∧
    (∀ n : ℕ, 2 ≤ n → Even n → (a n : ℚ) = (8 * (n : ℚ) ^ 3 + 24 * (n : ℚ) ^ 2 - 29 * (n : ℚ) + 54) / 6) ∧
    (∀ n : ℕ, 2 ≤ n → Odd n → (a n : ℚ) = (8 * (n : ℚ) ^ 3 + 24 * (n : ℚ) ^ 2 - 29 * (n : ℚ) + 57) / 6) ∧
    (∀ n : ℕ, 7 ≤ n → (a n : ℚ) = 3 * a (n - 1) - 2 * a (n - 2) - 2 * a (n - 3) + 3 * a (n - 4) - a (n - 5)) ∧
    (PowerSeries.mk (fun n => (a n : ℚ)) * ((1 - X) ^ 4 * (1 + X) : PowerSeries ℚ) = 1 + 2 * X + 13 * X ^ 2 + X ^ 3 - 3 * X ^ 4 + 7 * X ^ 5 - 5 * X ^ 6) := by
  sorry

end OMA.S_oeis_a273419

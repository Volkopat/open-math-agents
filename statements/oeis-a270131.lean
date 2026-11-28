import Mathlib

/-!
# A270131: Partial sums of the number of active (ON, black) cells in n-th stage of growth of two-dimensional cellular automaton defined by 'Rule 89', based on the 5-celled von Neumann neighborhood.

Source: https://oeis.org/A270131
Credit: @clementtrecourt

The conjectures listed in the entry, all stated below as one conjunction:
* a(n) = 1/12*(-39-9*(-1)^n+(22-24*(-1)^n)*n-12*(-2+(-1)^n)*n^2+8*n^3) for n>2.
* a(n) = (4*n^3+6*n^2-n-24)/6 for n>2 and n even.
* a(n) = (4*n^3+18*n^2+23*n-15)/6 for n>2 and n odd.
* a(n) = a(n-1)+3*a(n-2)-3*a(n-3)-3*a(n-4)+3*a(n-5)+a(n-6)-a(n-7) for n>9.
* G.f.: (1+4*x+2*x^2+32*x^3-12*x^4+x^5+14*x^6-10*x^7-5*x^8+5*x^9) / ((1-x)^4*(1+x)^3).

Conventions (as in Wolfram's numbering and the OEIS program): the automaton runs on the integer lattice ℤ², starting from one ON cell at (0, 0) on an all-OFF background, and the rule is applied to every cell, including the background, at each step (the OEIS program runs on a torus large enough that wrap-around never reaches the counted square).
Offset 0: a(n) is the sum over 0 <= k <= n of the number of ON cells in the square [-k, k] x [-k, k] after k steps.
The definition below reproduces every term listed in the OEIS entry. Each formula was checked against the automaton for every n up to 100.
-/

namespace OMA.S_oeis_a270131

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

/-- A270131(n): the sum over 0 <= k <= n of the number of ON cells in the square [-k, k] x [-k, k] after k steps. -/
def a (n : ℕ) : ℤ :=
  ∑ k ∈ Finset.range (n + 1), (onCount 89 k : ℤ)

open PowerSeries in
theorem main :
    (∀ n : ℕ, 3 ≤ n → (a n : ℚ) = 1 / 12 * (-39 - 9 * (-1 : ℚ) ^ n + (22 - 24 * (-1 : ℚ) ^ n) * (n : ℚ) - 12 * (-2 + (-1 : ℚ) ^ n) * (n : ℚ) ^ 2 + 8 * (n : ℚ) ^ 3)) ∧
    (∀ n : ℕ, 3 ≤ n → Even n → (a n : ℚ) = (4 * (n : ℚ) ^ 3 + 6 * (n : ℚ) ^ 2 - (n : ℚ) - 24) / 6) ∧
    (∀ n : ℕ, 3 ≤ n → Odd n → (a n : ℚ) = (4 * (n : ℚ) ^ 3 + 18 * (n : ℚ) ^ 2 + 23 * (n : ℚ) - 15) / 6) ∧
    (∀ n : ℕ, 10 ≤ n → (a n : ℚ) = a (n - 1) + 3 * a (n - 2) - 3 * a (n - 3) - 3 * a (n - 4) + 3 * a (n - 5) + a (n - 6) - a (n - 7)) ∧
    (PowerSeries.mk (fun n => (a n : ℚ)) * ((1 - X) ^ 4 * (1 + X) ^ 3 : PowerSeries ℚ) = 1 + 4 * X + 2 * X ^ 2 + 32 * X ^ 3 - 12 * X ^ 4 + X ^ 5 + 14 * X ^ 6 - 10 * X ^ 7 - 5 * X ^ 8 + 5 * X ^ 9) := by
  sorry

end OMA.S_oeis_a270131

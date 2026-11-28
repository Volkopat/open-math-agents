import Mathlib

/-!
# A270167: First differences of number of active (ON, black) cells in n-th stage of growth of two-dimensional cellular automaton defined by 'Rule 107', based on the 5-celled von Neumann neighborhood.

Source: https://oeis.org/A270167
Credit: @clementtrecourt

The conjectures listed in the entry, all stated below as one conjunction:
* a(n) = 9/2*(1+(-1)^n)+(4+6*(-1)^n)*n+3*(-1)^n*n^2 for n>7.
* a(n) = 3*n^2+10*n+9 for n>7 and even.
* a(n) = -3*n^2-2*n for n>7 and odd.
* a(n) = -a(n-1)+2*a(n-2)+2*a(n-3)-a(n-4)-a(n-5) for n>12.
* G.f.: (4+4*x+28*x^2-x^3-6*x^5-12*x^6+23*x^7+16*x^8-24*x^9-12*x^10+8*x^11+4*x^12) / ((1-x)^2*(1+x)^3).

Conventions (as in Wolfram's numbering and the OEIS program): the automaton runs on the integer lattice ℤ², starting from one ON cell at (0, 0) on an all-OFF background, and the rule is applied to every cell, including the background, at each step (the OEIS program runs on a torus large enough that wrap-around never reaches the counted square).
Offset 0: a(n) is c(n+1) - c(n), where c(t) is the number of ON cells in the square [-t, t] x [-t, t] after t steps.
The definition below reproduces every term listed in the OEIS entry. Each formula was checked against the automaton for every n up to 100.
-/

namespace OMA.S_oeis_a270167

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

/-- A270167(n): c(n+1) - c(n), where c(t) is the number of ON cells in the square [-t, t] x [-t, t] after t steps. -/
def a (n : ℕ) : ℤ :=
  (onCount 107 (n + 1) : ℤ) - onCount 107 n

open PowerSeries in
theorem main :
    (∀ n : ℕ, 8 ≤ n → (a n : ℚ) = 9 / 2 * (1 + (-1 : ℚ) ^ n) + (4 + 6 * (-1 : ℚ) ^ n) * (n : ℚ) + 3 * (-1 : ℚ) ^ n * (n : ℚ) ^ 2) ∧
    (∀ n : ℕ, 8 ≤ n → Even n → (a n : ℚ) = 3 * (n : ℚ) ^ 2 + 10 * (n : ℚ) + 9) ∧
    (∀ n : ℕ, 8 ≤ n → Odd n → (a n : ℚ) = -3 * (n : ℚ) ^ 2 - 2 * (n : ℚ)) ∧
    (∀ n : ℕ, 13 ≤ n → (a n : ℚ) = -a (n - 1) + 2 * a (n - 2) + 2 * a (n - 3) - a (n - 4) - a (n - 5)) ∧
    (PowerSeries.mk (fun n => (a n : ℚ)) * ((1 - X) ^ 2 * (1 + X) ^ 3 : PowerSeries ℚ) = 4 + 4 * X + 28 * X ^ 2 - X ^ 3 - 6 * X ^ 5 - 12 * X ^ 6 + 23 * X ^ 7 + 16 * X ^ 8 - 24 * X ^ 9 - 12 * X ^ 10 + 8 * X ^ 11 + 4 * X ^ 12) := by
  sorry

end OMA.S_oeis_a270167

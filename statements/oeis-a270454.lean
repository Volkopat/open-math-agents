import Mathlib

/-!
# A270454: Number of active (ON, black) cells in n-th stage of growth of two-dimensional cellular automaton defined by 'Rule 163', based on the 5-celled von Neumann neighborhood.

Source: https://oeis.org/A270454
Credit: @clementtrecourt

The conjectures listed in the entry, all stated below as one conjunction:
* a(n) = (1+(-1)^n+4*n-2*(-2+(-1)^n)*n^2)/2.
* a(n) = n^2+2*n+1 for n even.
* a(n) = 3*n^2+2*n for n odd.
* a(n) = 3*a(n-2)-3*a(n-4)+a(n-6) for n>5.
* G.f.: (1+5*x+6*x^2+18*x^3+x^4+x^5) / ((1-x)^3*(1+x)^3).

Conventions (as in Wolfram's numbering and the OEIS program): the automaton runs on the integer lattice ℤ², starting from one ON cell at (0, 0) on an all-OFF background, and the rule is applied to every cell, including the background, at each step (the OEIS program runs on a torus large enough that wrap-around never reaches the counted square).
Offset 0: a(n) is the number of ON cells in the square [-n, n] x [-n, n] after n steps.
The definition below reproduces every term listed in the OEIS entry. Each formula was checked against the automaton for every n up to 100.
-/

namespace OMA.S_oeis_a270454

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

/-- A270454(n): the number of ON cells in the square [-n, n] x [-n, n] after n steps. -/
def a (n : ℕ) : ℤ :=
  (onCount 163 n : ℤ)

open PowerSeries in
theorem main :
    (∀ n : ℕ, (a n : ℚ) = (1 + (-1 : ℚ) ^ n + 4 * (n : ℚ) - 2 * (-2 + (-1 : ℚ) ^ n) * (n : ℚ) ^ 2) / 2) ∧
    (∀ n : ℕ, Even n → (a n : ℚ) = (n : ℚ) ^ 2 + 2 * (n : ℚ) + 1) ∧
    (∀ n : ℕ, Odd n → (a n : ℚ) = 3 * (n : ℚ) ^ 2 + 2 * (n : ℚ)) ∧
    (∀ n : ℕ, 6 ≤ n → (a n : ℚ) = 3 * a (n - 2) - 3 * a (n - 4) + a (n - 6)) ∧
    (PowerSeries.mk (fun n => (a n : ℚ)) * ((1 - X) ^ 3 * (1 + X) ^ 3 : PowerSeries ℚ) = 1 + 5 * X + 6 * X ^ 2 + 18 * X ^ 3 + X ^ 4 + X ^ 5) := by
  sorry

end OMA.S_oeis_a270454

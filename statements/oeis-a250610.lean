import Mathlib

/-!
# OEIS A250610

Source: https://oeis.org/A250610
Credit: @schulzee (agent: Claude Code, model claude-fable-5-2)

A250610: Number of (n+1) X (7+1) 0..1 arrays with nondecreasing x(i,j)-x(i,j-1) in the i direction and nondecreasing x(i,j)-x(i-1,j) in the j direction.

Data (offset 1): 1013, 2336, 4353, 7320, 11749, 18664, 30113, 50192, 87093, 157200, 293281

Conjectures in the entry (R. H. Hardin, empirical; Colin Barker, conjectures):
  Empirical: a(n) = 5*a(n-1) - 9*a(n-2) + 7*a(n-3) - 2*a(n-4).
  Conjectures from _Colin Barker_, Nov 15 2018: (Start)
  G.f.: x*(1013 - 2729*x + 1790*x^2 - 512*x^3) / ((1 - x)^3*(1 - 2*x)). - _Colin Barker_, Nov 15 2018
  a(n) = 128 + 2^(7+n) + 410*n + 219*n^2.
  (End)

Formalization notes.
* An array is a function `x : Fin (n + 1) → Fin 8 → Fin 2`, `x i j` is the entry in row `i` and column `j`.
* The condition `nondecreasing f in the i direction` compares rows `i` and `i+1`, the condition
  `nondecreasing g in the j direction` compares columns `j` and `j+1`. Each of the two conditions
  is a condition on the 2 X 2 blocks of adjacent rows and columns, see `Blk`. With this reading
  the counts agree with all terms of the OEIS data (checked by an independent computation).
* `main` states the first terms and the linear recurrence
  a(n) = +5*a(n-1) -9*a(n-2) +7*a(n-3) -2*a(n-4) for n > 4.
  The first terms together with the recurrence are equivalent to the conjectured generating
  function.
* `main` also states the empirical closed form a(n) = 128 + 2^(7+n) + 410*n + 219*n^2 (multiplied by 1).
-/

namespace OMA.S_oeis_a250610

/-- The condition on one 2 X 2 block with entries `a b` (upper row) and `c d` (lower row):
`x(i,j)-x(i,j-1)` does not decrease from the upper row to the lower row, and
`x(i,j)-x(i-1,j)` does not decrease from the left column to the right column. -/
def Blk (a b c d : Fin 2) : Prop :=
    ((d : ℕ) : ℤ) - ((c : ℕ) : ℤ) ≥ ((b : ℕ) : ℤ) - ((a : ℕ) : ℤ) ∧
    ((d : ℕ) : ℤ) - ((b : ℕ) : ℤ) ≥ ((c : ℕ) : ℤ) - ((a : ℕ) : ℤ)

/-- `x` is an array with entries in `0..1`; the first index is the row `i`, the second index is
the column `j`. The array is admissible when every 2 X 2 block of adjacent rows and columns
satisfies `Blk`. -/
def Good (n : ℕ) (x : Fin (n + 1) → Fin 8 → Fin 2) : Prop :=
  ∀ (i : Fin n) (j : Fin 7),
    Blk (x i.castSucc j.castSucc) (x i.castSucc j.succ) (x i.succ j.castSucc) (x i.succ j.succ)

/-- `a n` is the number of admissible (n+1) X 8 arrays. -/
noncomputable def a (n : ℕ) : ℕ := Nat.card {x : Fin (n + 1) → Fin 8 → Fin 2 // Good n x}

theorem main : a 1 = 1013 ∧ a 2 = 2336 ∧ a 3 = 4353 ∧ a 4 = 7320 ∧
    (∀ n : ℕ, 1 ≤ n → (a (n + 4) : ℤ) = 5 * a (n + 3) - 9 * a (n + 2) + 7 * a (n + 1) - 2 * a n) ∧
    (∀ n : ℕ, 1 ≤ n → 1 * (a n : ℤ) = 128 + 2 ^ (n + 7) + 410 * ((n : ℕ) : ℤ) + 219 * ((n : ℕ) : ℤ) ^ 2) := by
  sorry

end OMA.S_oeis_a250610

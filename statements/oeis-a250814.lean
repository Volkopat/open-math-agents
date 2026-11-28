import Mathlib

/-!
# OEIS A250814

Source: https://oeis.org/A250814
Credit: @schulzee (agent: Claude Code, model claude-fable-5-2)

A250814: Number of (2+1) X (n+1) 0..2 arrays with nondecreasing x(i,j)-x(i,j-1) in the i direction and nondecreasing min(x(i,j),x(i-1,j)) in the j direction.

Data (offset 1): 129, 379, 873, 1731, 3097, 5139, 8049, 12043, 17361, 24267, 33049, 44019, 57513

Conjectures in the entry (R. H. Hardin, empirical; Colin Barker, conjectures):
  Empirical: a(n) = 1*n^4 + 10*n^3 + 37*n^2 + 54*n + 27.
  Conjectures from _Colin Barker_, Nov 21 2018: (Start)
  G.f.: x*(129 - 266*x + 268*x^2 - 134*x^3 + 27*x^4) / (1 - x)^5.
  a(n) = 5*a(n-1) - 10*a(n-2) + 10*a(n-3) - 5*a(n-4) + a(n-5) for n>5.
  (End)

Formalization notes.
* An array is a function `x : Fin 3 → Fin (n + 1) → Fin 3`, `x i j` is the entry in row `i` and column `j`.
* The condition `nondecreasing f in the i direction` compares rows `i` and `i+1`, the condition
  `nondecreasing g in the j direction` compares columns `j` and `j+1`. Each of the two conditions
  is a condition on the 2 X 2 blocks of adjacent rows and columns, see `Blk`. With this reading
  the counts agree with all terms of the OEIS data (checked by an independent computation).
* `main` states the first terms and the linear recurrence
  a(n) = +5*a(n-1) -10*a(n-2) +10*a(n-3) -5*a(n-4) +1*a(n-5) for n > 5.
  The first terms together with the recurrence are equivalent to the conjectured generating
  function.
* `main` also states the empirical closed form a(n) = n^4 + 10*n^3 + 37*n^2 + 54*n + 27 (multiplied by 1).
-/

namespace OMA.S_oeis_a250814

/-- The condition on one 2 X 2 block with entries `a b` (upper row) and `c d` (lower row):
`x(i,j)-x(i,j-1)` does not decrease from the upper row to the lower row, and
`min(x(i,j),x(i-1,j))` does not decrease from the left column to the right column. -/
def Blk (a b c d : Fin 3) : Prop :=
    ((d : ℕ) : ℤ) - ((c : ℕ) : ℤ) ≥ ((b : ℕ) : ℤ) - ((a : ℕ) : ℤ) ∧
    min (d : ℕ) (b : ℕ) ≥ min (c : ℕ) (a : ℕ)

/-- `x` is an array with entries in `0..2`; the first index is the row `i`, the second index is
the column `j`. The array is admissible when every 2 X 2 block of adjacent rows and columns
satisfies `Blk`. -/
def Good (n : ℕ) (x : Fin 3 → Fin (n + 1) → Fin 3) : Prop :=
  ∀ (i : Fin 2) (j : Fin n),
    Blk (x i.castSucc j.castSucc) (x i.castSucc j.succ) (x i.succ j.castSucc) (x i.succ j.succ)

/-- `a n` is the number of admissible 3 X (n+1) arrays. -/
noncomputable def a (n : ℕ) : ℕ := Nat.card {x : Fin 3 → Fin (n + 1) → Fin 3 // Good n x}

theorem main : a 1 = 129 ∧ a 2 = 379 ∧ a 3 = 873 ∧ a 4 = 1731 ∧ a 5 = 3097 ∧
    (∀ n : ℕ, 1 ≤ n → (a (n + 5) : ℤ) = 5 * a (n + 4) - 10 * a (n + 3) + 10 * a (n + 2) - 5 * a (n + 1) + a n) ∧
    (∀ n : ℕ, 1 ≤ n → 1 * (a n : ℤ) = (n : ℤ) ^ 4 + 10 * n ^ 3 + 37 * n ^ 2 + 54 * n + 27) := by
  sorry

end OMA.S_oeis_a250814

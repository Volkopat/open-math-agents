import Mathlib

/-!
# OEIS A250658

Source: https://oeis.org/A250658
Credit: @schulzee (agent: Claude Code, model claude-fable-5-2)

A250658: Number of (4+1) X (n+1) 0..1 arrays with nondecreasing x(i,j)-x(i,j-1) in the i direction and nondecreasing min(x(i,j),x(i-1,j)) in the j direction.

Data (offset 1): 79, 142, 221, 316, 427, 554, 697, 856, 1031, 1222, 1429, 1652, 1891, 2146, 2417

Conjectures in the entry (R. H. Hardin, empirical; Colin Barker, conjectures):
  Empirical: a(n) = 8*n^2 + 39*n + 32.
  Conjectures from _Colin Barker_, Nov 15 2018: (Start)
  G.f.: x*(79 - 95*x + 32*x^2) / (1 - x)^3.
  a(n) = 3*a(n-1) - 3*a(n-2) + a(n-3) for n>3.
  (End)

Formalization notes.
* An array is a function `x : Fin 5 → Fin (n + 1) → Fin 2`, `x i j` is the entry in row `i` and column `j`.
* The condition `nondecreasing f in the i direction` compares rows `i` and `i+1`, the condition
  `nondecreasing g in the j direction` compares columns `j` and `j+1`. Each of the two conditions
  is a condition on the 2 X 2 blocks of adjacent rows and columns, see `Blk`. With this reading
  the counts agree with all terms of the OEIS data (checked by an independent computation).
* `main` states the first terms and the linear recurrence
  a(n) = +3*a(n-1) -3*a(n-2) +1*a(n-3) for n > 3.
  The first terms together with the recurrence are equivalent to the conjectured generating
  function.
* `main` also states the empirical closed form a(n) = 8*n^2 + 39*n + 32 (multiplied by 1).
-/

namespace OMA.S_oeis_a250658

/-- The condition on one 2 X 2 block with entries `a b` (upper row) and `c d` (lower row):
`x(i,j)-x(i,j-1)` does not decrease from the upper row to the lower row, and
`min(x(i,j),x(i-1,j))` does not decrease from the left column to the right column. -/
def Blk (a b c d : Fin 2) : Prop :=
    ((d : ℕ) : ℤ) - ((c : ℕ) : ℤ) ≥ ((b : ℕ) : ℤ) - ((a : ℕ) : ℤ) ∧
    min (d : ℕ) (b : ℕ) ≥ min (c : ℕ) (a : ℕ)

/-- `x` is an array with entries in `0..1`; the first index is the row `i`, the second index is
the column `j`. The array is admissible when every 2 X 2 block of adjacent rows and columns
satisfies `Blk`. -/
def Good (n : ℕ) (x : Fin 5 → Fin (n + 1) → Fin 2) : Prop :=
  ∀ (i : Fin 4) (j : Fin n),
    Blk (x i.castSucc j.castSucc) (x i.castSucc j.succ) (x i.succ j.castSucc) (x i.succ j.succ)

/-- `a n` is the number of admissible 5 X (n+1) arrays. -/
noncomputable def a (n : ℕ) : ℕ := Nat.card {x : Fin 5 → Fin (n + 1) → Fin 2 // Good n x}

theorem main : a 1 = 79 ∧ a 2 = 142 ∧ a 3 = 221 ∧
    (∀ n : ℕ, 1 ≤ n → (a (n + 3) : ℤ) = 3 * a (n + 2) - 3 * a (n + 1) + a n) ∧
    (∀ n : ℕ, 1 ≤ n → 1 * (a n : ℤ) = 8 * (n : ℤ) ^ 2 + 39 * n + 32) := by
  sorry

end OMA.S_oeis_a250658

import Mathlib

/-!
# OEIS A250784

Source: https://oeis.org/A250784
Credit: @schulzee (agent: Claude Code, model claude-fable-5-2)

A250784: Number of (2+1) X (n+1) 0..1 arrays with nondecreasing x(i,j)+x(i,j-1) in the i direction and nondecreasing absolute value of x(i,j)-x(i-1,j) in the j direction.

Data (offset 1): 18, 46, 106, 238, 518, 1106, 2326, 4838, 9978, 20446, 41686, 84658, 171398

Conjectures in the entry (R. H. Hardin, empirical; Colin Barker, conjectures):
  Empirical: a(n) = 4*a(n-1) - 4*a(n-2) - a(n-3) + 2*a(n-4).
  Conjectures from _Colin Barker_, Nov 19 2018: (Start)
  G.f.: 2*x*(9 - 13*x - 3*x^2 + 8*x^3) / ((1 - x)*(1 - 2*x)*(1 - x - x^2)).
  a(n) = 2^(1-n) * (2^n*(1+11*2^n) + 2*(1-sqrt(5))^n*(-2+sqrt(5)) - 2*(1+sqrt(5))^n*(2+sqrt(5))).
  (End)

Formalization notes.
* An array is a function `x : Fin 3 → Fin (n + 1) → Fin 2`, `x i j` is the entry in row `i` and column `j`.
* The condition `nondecreasing f in the i direction` compares rows `i` and `i+1`, the condition
  `nondecreasing g in the j direction` compares columns `j` and `j+1`. Each of the two conditions
  is a condition on the 2 X 2 blocks of adjacent rows and columns, see `Blk`. With this reading
  the counts agree with all terms of the OEIS data (checked by an independent computation).
* `main` states the first terms and the linear recurrence
  a(n) = +4*a(n-1) -4*a(n-2) -1*a(n-3) +2*a(n-4) for n > 4.
  The first terms together with the recurrence are equivalent to the conjectured generating
  function.
-/

namespace OMA.S_oeis_a250784

/-- The condition on one 2 X 2 block with entries `a b` (upper row) and `c d` (lower row):
`x(i,j)+x(i,j-1)` does not decrease from the upper row to the lower row, and
`the absolute value of x(i,j)-x(i-1,j)` does not decrease from the left column to the right column. -/
def Blk (a b c d : Fin 2) : Prop :=
    (d : ℕ) + (c : ℕ) ≥ (b : ℕ) + (a : ℕ) ∧
    (((d : ℕ) : ℤ) - ((b : ℕ) : ℤ)).natAbs ≥ (((c : ℕ) : ℤ) - ((a : ℕ) : ℤ)).natAbs

/-- `x` is an array with entries in `0..1`; the first index is the row `i`, the second index is
the column `j`. The array is admissible when every 2 X 2 block of adjacent rows and columns
satisfies `Blk`. -/
def Good (n : ℕ) (x : Fin 3 → Fin (n + 1) → Fin 2) : Prop :=
  ∀ (i : Fin 2) (j : Fin n),
    Blk (x i.castSucc j.castSucc) (x i.castSucc j.succ) (x i.succ j.castSucc) (x i.succ j.succ)

/-- `a n` is the number of admissible 3 X (n+1) arrays. -/
noncomputable def a (n : ℕ) : ℕ := Nat.card {x : Fin 3 → Fin (n + 1) → Fin 2 // Good n x}

theorem main : a 1 = 18 ∧ a 2 = 46 ∧ a 3 = 106 ∧ a 4 = 238 ∧
    (∀ n : ℕ, 1 ≤ n → (a (n + 4) : ℤ) = 4 * a (n + 3) - 4 * a (n + 2) - a (n + 1) + 2 * a n) := by
  sorry

end OMA.S_oeis_a250784

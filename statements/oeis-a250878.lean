import Mathlib

/-!
# OEIS A250878

Source: https://oeis.org/A250878
Credit: @schulzee (agent: Claude Code, model claude-fable-5-2)

A250878: Number of (1+1) X (n+1) 0..3 arrays with nondecreasing x(i,j)-x(i,j-1) in the i direction and nondecreasing x(i,j)+x(i-1,j) in the j direction.

Data (offset 1): 90, 288, 678, 1328, 2306, 3680, 5518, 7888, 10858, 14496, 18870, 24048, 30098

Conjectures in the entry (R. H. Hardin, empirical; Colin Barker, conjectures):
  Empirical: a(n) = (34/3)*n^3 + 28*n^2 + (104/3)*n + 16.
  Conjectures from _Colin Barker_, Nov 22 2018: (Start)
  G.f.: 2*x*(45 - 36*x + 33*x^2 - 8*x^3) / (1 - x)^4.
  a(n) = 4*a(n-1) - 6*a(n-2) + 4*a(n-3) - a(n-4) for n>4.
  (End)

Formalization notes.
* An array is a function `x : Fin 2 → Fin (n + 1) → Fin 4`, `x i j` is the entry in row `i` and column `j`.
* The condition `nondecreasing f in the i direction` compares rows `i` and `i+1`, the condition
  `nondecreasing g in the j direction` compares columns `j` and `j+1`. Each of the two conditions
  is a condition on the 2 X 2 blocks of adjacent rows and columns, see `Blk`. With this reading
  the counts agree with all terms of the OEIS data (checked by an independent computation).
* `main` states the first terms and the linear recurrence
  a(n) = +4*a(n-1) -6*a(n-2) +4*a(n-3) -1*a(n-4) for n > 4.
  The first terms together with the recurrence are equivalent to the conjectured generating
  function.
* `main` also states the empirical closed form a(n) = (34/3)*n^3 + 28*n^2 + (104/3)*n + 16 (multiplied by 3).
-/

namespace OMA.S_oeis_a250878

/-- The condition on one 2 X 2 block with entries `a b` (upper row) and `c d` (lower row):
`x(i,j)-x(i,j-1)` does not decrease from the upper row to the lower row, and
`x(i,j)+x(i-1,j)` does not decrease from the left column to the right column. -/
def Blk (a b c d : Fin 4) : Prop :=
    ((d : ℕ) : ℤ) - ((c : ℕ) : ℤ) ≥ ((b : ℕ) : ℤ) - ((a : ℕ) : ℤ) ∧
    (d : ℕ) + (b : ℕ) ≥ (c : ℕ) + (a : ℕ)

/-- `x` is an array with entries in `0..3`; the first index is the row `i`, the second index is
the column `j`. The array is admissible when every 2 X 2 block of adjacent rows and columns
satisfies `Blk`. -/
def Good (n : ℕ) (x : Fin 2 → Fin (n + 1) → Fin 4) : Prop :=
  ∀ (i : Fin 1) (j : Fin n),
    Blk (x i.castSucc j.castSucc) (x i.castSucc j.succ) (x i.succ j.castSucc) (x i.succ j.succ)

/-- `a n` is the number of admissible 2 X (n+1) arrays. -/
noncomputable def a (n : ℕ) : ℕ := Nat.card {x : Fin 2 → Fin (n + 1) → Fin 4 // Good n x}

theorem main : a 1 = 90 ∧ a 2 = 288 ∧ a 3 = 678 ∧ a 4 = 1328 ∧
    (∀ n : ℕ, 1 ≤ n → (a (n + 4) : ℤ) = 4 * a (n + 3) - 6 * a (n + 2) + 4 * a (n + 1) - a n) ∧
    (∀ n : ℕ, 1 ≤ n → 3 * (a n : ℤ) = 34 * (n : ℤ) ^ 3 + 84 * n ^ 2 + 104 * n + 48) := by
  sorry

end OMA.S_oeis_a250878

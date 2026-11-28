import Mathlib

/-!
# OEIS A250894

Source: https://oeis.org/A250894
Credit: @schulzee (agent: Claude Code, model claude-fable-5-2)

A250894: Number of (n+1) X (4+1) 0..2 arrays with nondecreasing x(i,j)-x(i,j-1) in the i direction and nondecreasing absolute value of x(i,j)-x(i-1,j) in the j direction.

Data (offset 1): 1229, 3867, 12387, 39003, 119359, 357335, 1052787, 3069907, 8903447, 25780959

Conjectures in the entry (R. H. Hardin, empirical; Colin Barker, conjectures):
  Empirical: a(n) = 12*a(n-1) - 60*a(n-2) + 162*a(n-3) - 255*a(n-4) + 234*a(n-5) - 116*a(n-6) + 24*a(n-7) for n>9.
  Conjectures from _Colin Barker_, Nov 23 2018: (Start)
  G.f.: x*(1229 - 10881*x + 39723*x^2 - 76719*x^3 + 81484*x^4 - 42988*x^5 + 4192*x^6 + 6688*x^7 - 2560*x^8) / ((1 - x)^3*(1 - 2*x)^3*(1 - 3*x)).
  a(n) = -265 - 21*2^n + 9604*3^(-3+n) + (226-9*2^(3+n))*n + 6*(7+9*2^n)*n^2 for n>2.
  (End)

Formalization notes.
* An array is a function `x : Fin (n + 1) → Fin 5 → Fin 3`, `x i j` is the entry in row `i` and column `j`.
* The condition `nondecreasing f in the i direction` compares rows `i` and `i+1`, the condition
  `nondecreasing g in the j direction` compares columns `j` and `j+1`. Each of the two conditions
  is a condition on the 2 X 2 blocks of adjacent rows and columns, see `Blk`. With this reading
  the counts agree with all terms of the OEIS data (checked by an independent computation).
* `main` states the first terms and the linear recurrence
  a(n) = +12*a(n-1) -60*a(n-2) +162*a(n-3) -255*a(n-4) +234*a(n-5) -116*a(n-6) +24*a(n-7) for n > 9.
  The first terms together with the recurrence are equivalent to the conjectured generating
  function.
-/

namespace OMA.S_oeis_a250894

/-- The condition on one 2 X 2 block with entries `a b` (upper row) and `c d` (lower row):
`x(i,j)-x(i,j-1)` does not decrease from the upper row to the lower row, and
`the absolute value of x(i,j)-x(i-1,j)` does not decrease from the left column to the right column. -/
def Blk (a b c d : Fin 3) : Prop :=
    ((d : ℕ) : ℤ) - ((c : ℕ) : ℤ) ≥ ((b : ℕ) : ℤ) - ((a : ℕ) : ℤ) ∧
    (((d : ℕ) : ℤ) - ((b : ℕ) : ℤ)).natAbs ≥ (((c : ℕ) : ℤ) - ((a : ℕ) : ℤ)).natAbs

/-- `x` is an array with entries in `0..2`; the first index is the row `i`, the second index is
the column `j`. The array is admissible when every 2 X 2 block of adjacent rows and columns
satisfies `Blk`. -/
def Good (n : ℕ) (x : Fin (n + 1) → Fin 5 → Fin 3) : Prop :=
  ∀ (i : Fin n) (j : Fin 4),
    Blk (x i.castSucc j.castSucc) (x i.castSucc j.succ) (x i.succ j.castSucc) (x i.succ j.succ)

/-- `a n` is the number of admissible (n+1) X 5 arrays. -/
noncomputable def a (n : ℕ) : ℕ := Nat.card {x : Fin (n + 1) → Fin 5 → Fin 3 // Good n x}

theorem main : a 1 = 1229 ∧ a 2 = 3867 ∧ a 3 = 12387 ∧ a 4 = 39003 ∧ a 5 = 119359 ∧ a 6 = 357335 ∧ a 7 = 1052787 ∧ a 8 = 3069907 ∧ a 9 = 8903447 ∧
    (∀ n : ℕ, 3 ≤ n → (a (n + 7) : ℤ) = 12 * a (n + 6) - 60 * a (n + 5) + 162 * a (n + 4) - 255 * a (n + 3) + 234 * a (n + 2) - 116 * a (n + 1) + 24 * a n) := by
  sorry

end OMA.S_oeis_a250894

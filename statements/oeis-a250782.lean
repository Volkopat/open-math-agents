import Mathlib

/-!
# OEIS A250782

Source: https://oeis.org/A250782
Credit: @schulzee (agent: Claude Code, model claude-fable-5-2)

A250782: Number of (n+1) X (7+1) 0..1 arrays with nondecreasing x(i,j)+x(i,j-1) in the i direction and nondecreasing absolute value of x(i,j)-x(i-1,j) in the j direction.

Data (offset 1): 901, 2326, 5568, 12796, 28692, 63184, 137082, 293588, 621664, 1303276, 2708612

Conjectures in the entry (R. H. Hardin, empirical; Colin Barker, conjectures):
  Empirical: a(n) = 12*a(n-1) - 65*a(n-2) + 210*a(n-3) - 450*a(n-4) + 672*a(n-5) - 714*a(n-6) + 540*a(n-7) - 285*a(n-8) + 100*a(n-9) - 21*a(n-10) + 2*a(n-11).
  Conjectures from _Colin Barker_, Nov 19 2018: (Start)
  G.f.: x*(901 - 8486*x + 36221*x^2 - 92040*x^3 + 154050*x^4 - 177432*x^5 + 142536*x^6 - 79028*x^7 + 29083*x^8 - 6482*x^9 + 681*x^10) / ((1 - x)^10*(1 - 2*x)).
  a(n) = (45360*(3025*2^n-2344) - 70509024*n - 9423432*n^2 - 6541100*n^3 + 254142*n^4 - 151725*n^5 + 6552*n^6 - 870*n^7 + 18*n^8 - n^9) / 90720.
  (End)

Formalization notes.
* An array is a function `x : Fin (n + 1) → Fin 8 → Fin 2`, `x i j` is the entry in row `i` and column `j`.
* The condition `nondecreasing f in the i direction` compares rows `i` and `i+1`, the condition
  `nondecreasing g in the j direction` compares columns `j` and `j+1`. Each of the two conditions
  is a condition on the 2 X 2 blocks of adjacent rows and columns, see `Blk`. With this reading
  the counts agree with all terms of the OEIS data (checked by an independent computation).
* `main` states the first terms and the linear recurrence
  a(n) = +12*a(n-1) -65*a(n-2) +210*a(n-3) -450*a(n-4) +672*a(n-5) -714*a(n-6) +540*a(n-7) -285*a(n-8) +100*a(n-9) -21*a(n-10) +2*a(n-11) for n > 11.
  The first terms together with the recurrence are equivalent to the conjectured generating
  function.
-/

namespace OMA.S_oeis_a250782

/-- The condition on one 2 X 2 block with entries `a b` (upper row) and `c d` (lower row):
`x(i,j)+x(i,j-1)` does not decrease from the upper row to the lower row, and
`the absolute value of x(i,j)-x(i-1,j)` does not decrease from the left column to the right column. -/
def Blk (a b c d : Fin 2) : Prop :=
    (d : ℕ) + (c : ℕ) ≥ (b : ℕ) + (a : ℕ) ∧
    (((d : ℕ) : ℤ) - ((b : ℕ) : ℤ)).natAbs ≥ (((c : ℕ) : ℤ) - ((a : ℕ) : ℤ)).natAbs

/-- `x` is an array with entries in `0..1`; the first index is the row `i`, the second index is
the column `j`. The array is admissible when every 2 X 2 block of adjacent rows and columns
satisfies `Blk`. -/
def Good (n : ℕ) (x : Fin (n + 1) → Fin 8 → Fin 2) : Prop :=
  ∀ (i : Fin n) (j : Fin 7),
    Blk (x i.castSucc j.castSucc) (x i.castSucc j.succ) (x i.succ j.castSucc) (x i.succ j.succ)

/-- `a n` is the number of admissible (n+1) X 8 arrays. -/
noncomputable def a (n : ℕ) : ℕ := Nat.card {x : Fin (n + 1) → Fin 8 → Fin 2 // Good n x}

theorem main : a 1 = 901 ∧ a 2 = 2326 ∧ a 3 = 5568 ∧ a 4 = 12796 ∧ a 5 = 28692 ∧ a 6 = 63184 ∧ a 7 = 137082 ∧ a 8 = 293588 ∧ a 9 = 621664 ∧ a 10 = 1303276 ∧ a 11 = 2708612 ∧
    (∀ n : ℕ, 1 ≤ n → (a (n + 11) : ℤ) = 12 * a (n + 10) - 65 * a (n + 9) + 210 * a (n + 8) - 450 * a (n + 7) + 672 * a (n + 6) - 714 * a (n + 5) + 540 * a (n + 4) - 285 * a (n + 3) + 100 * a (n + 2) - 21 * a (n + 1) + 2 * a n) := by
  sorry

end OMA.S_oeis_a250782

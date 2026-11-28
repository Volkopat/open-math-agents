import Mathlib

/-!
# OEIS A250854

Source: https://oeis.org/A250854
Credit: @schulzee (agent: Claude Code, model claude-fable-5-2)

A250854: Number of (2+1) X (n+1) 0..3 arrays with nondecreasing x(i,j)-x(i,j-1) in the i direction and nondecreasing min(x(i,j),x(i-1,j)) in the j direction.

Data (offset 1): 543, 2457, 8037, 21436, 49599, 103293, 198297, 356752, 608671, 993609, 1562493

Conjectures in the entry (R. H. Hardin, empirical; Colin Barker, conjectures):
  Empirical: a(n) = (2/9)*n^6 + (47/12)*n^5 + (953/36)*n^4 + (1141/12)*n^3 + (6527/36)*n^2 + 172*n + 64.
  Conjectures from _Colin Barker_, Nov 21 2018: (Start)
  G.f.: x*(543 - 1344*x + 2241*x^2 - 2231*x^3 + 1334*x^4 - 447*x^5 + 64*x^6) / (1 - x)^7.
  a(n) = 7*a(n-1) - 21*a(n-2) + 35*a(n-3) - 35*a(n-4) + 21*a(n-5) - 7*a(n-6) + a(n-7) for n>7.
  (End)

Formalization notes.
* An array is a function `x : Fin 3 → Fin (n + 1) → Fin 4`, `x i j` is the entry in row `i` and column `j`.
* The condition `nondecreasing f in the i direction` compares rows `i` and `i+1`, the condition
  `nondecreasing g in the j direction` compares columns `j` and `j+1`. Each of the two conditions
  is a condition on the 2 X 2 blocks of adjacent rows and columns, see `Blk`. With this reading
  the counts agree with all terms of the OEIS data (checked by an independent computation).
* `main` states the first terms and the linear recurrence
  a(n) = +7*a(n-1) -21*a(n-2) +35*a(n-3) -35*a(n-4) +21*a(n-5) -7*a(n-6) +1*a(n-7) for n > 7.
  The first terms together with the recurrence are equivalent to the conjectured generating
  function.
* `main` also states the empirical closed form a(n) = (2/9)*n^6 + (47/12)*n^5 + (953/36)*n^4 + (1141/12)*n^3 + (6527/36)*n^2 + 172*n + 64 (multiplied by 36).
-/

namespace OMA.S_oeis_a250854

/-- The condition on one 2 X 2 block with entries `a b` (upper row) and `c d` (lower row):
`x(i,j)-x(i,j-1)` does not decrease from the upper row to the lower row, and
`min(x(i,j),x(i-1,j))` does not decrease from the left column to the right column. -/
def Blk (a b c d : Fin 4) : Prop :=
    ((d : ℕ) : ℤ) - ((c : ℕ) : ℤ) ≥ ((b : ℕ) : ℤ) - ((a : ℕ) : ℤ) ∧
    min (d : ℕ) (b : ℕ) ≥ min (c : ℕ) (a : ℕ)

/-- `x` is an array with entries in `0..3`; the first index is the row `i`, the second index is
the column `j`. The array is admissible when every 2 X 2 block of adjacent rows and columns
satisfies `Blk`. -/
def Good (n : ℕ) (x : Fin 3 → Fin (n + 1) → Fin 4) : Prop :=
  ∀ (i : Fin 2) (j : Fin n),
    Blk (x i.castSucc j.castSucc) (x i.castSucc j.succ) (x i.succ j.castSucc) (x i.succ j.succ)

/-- `a n` is the number of admissible 3 X (n+1) arrays. -/
noncomputable def a (n : ℕ) : ℕ := Nat.card {x : Fin 3 → Fin (n + 1) → Fin 4 // Good n x}

theorem main : a 1 = 543 ∧ a 2 = 2457 ∧ a 3 = 8037 ∧ a 4 = 21436 ∧ a 5 = 49599 ∧ a 6 = 103293 ∧ a 7 = 198297 ∧
    (∀ n : ℕ, 1 ≤ n → (a (n + 7) : ℤ) = 7 * a (n + 6) - 21 * a (n + 5) + 35 * a (n + 4) - 35 * a (n + 3) + 21 * a (n + 2) - 7 * a (n + 1) + a n) ∧
    (∀ n : ℕ, 1 ≤ n → 36 * (a n : ℤ) = 8 * (n : ℤ) ^ 6 + 141 * n ^ 5 + 953 * n ^ 4 + 3423 * n ^ 3 + 6527 * n ^ 2 + 6192 * n + 2304) := by
  sorry

end OMA.S_oeis_a250854

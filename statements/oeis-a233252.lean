import Mathlib

/-!
# A233252: Number of n X 4 0..5 arrays with no element x(i,j) adjacent to itself or value 5-x(i,j) horizontally or antidiagonally, top left element zero, and 1 appearing before 2 3 and 4, and 2 appearing before 3 in row major order (unlabelled 6-colorings with no clashing color pairs).

Source: https://oeis.org/A233252
Credit: @Salofe

The sequence is due to R. H. Hardin (Dec 06 2013); it is column 4 of A233256.

Conjectures from Colin Barker, Oct 10 2018, quoted verbatim from the entry:
* "G.f.: 2*x*(5 - 208*x) / ((1 - 16*x)*(1 - 144*x))."
* "a(n) = 2^(4*n-3) * (4*9^n+9) / 9."

The entry also lists Hardin's "Empirical: a(n) = 160*a(n-1) - 2304*a(n-2)."; that recurrence is
not part of this statement, which states Barker's two conjectures only.

Formalization notes:
* Offset 1, as in the entry (data: 10, 1184, 166400, 23896064, ...). The value `a 0` is never
  used: the formula is stated for n ≥ 1, and the g.f. has coefficient 0 at x^0. (With the
  definitions below `a 0 = 1`, the empty array.)
* An n X 4 0..5 array is a function `x : Fin n → Fin 4 → Fin 6`; `x i j` is the entry in row `i`
  (rows numbered from top to bottom) and column `j` (columns numbered from left to right).
  Arrays are labelled: they are not identified up to symmetry (the definition already picks one
  representative of each class of colorings through the conditions on the order of first
  appearances, which is why the entry calls them unlabelled).
* "Adjacent to itself or value 5-x(i,j)": two entries `u`, `v` clash (`Clash`) when `v = u` or
  `v = 5 - u`, i.e. `u + v = 5` (for entries in 0..5). The relation is symmetric, so it is
  required once for each pair of neighbouring cells: horizontally `(i, j)` and `(i, j + 1)`, and
  antidiagonally `(i, j + 1)` and `(i + 1, j)` (the line from top right to bottom left). Vertical
  and diagonal neighbours are not constrained.
* "Top left element zero": `x 0 0 = 0` (for n ≥ 1).
* Row-major order: the cell `(i', j')` comes before the cell `(i, j)` (`Before`) when `i' < i`, or
  `i' = i` and `j' < j`. "u appearing before v" (`AppearsBefore x u v`) means that every cell
  with value `v` comes after some cell with value `u`, i.e. the first `u` comes before the first
  `v`. It holds vacuously when `v` does not appear (and does not require `u` to appear then).
  The definition asks this for (u, v) = (1, 2), (1, 3), (1, 4) and (2, 3).
* This reading reproduces the data. An exhaustive enumeration of all 6^(4n) arrays, computing
  exactly the definitions below, gives 10, 1184, 166400 for n = 1, 2, 3, and a row-by-row count
  of the same definition gives all 210 terms of the b-file (n = 1..210). The five 2 X 4 solutions
  shown in the entry satisfy `Good`. The stricter reading that also requires 2 to appear would
  give 6 and 1120 for n = 1, 2. Using the diagonal `(i, j)`, `(i + 1, j + 1)` instead of the
  antidiagonal gives the same counts but rejects the fifth example (its entries 2 at `(0, 2)` and
  3 at `(1, 3)` clash).
* The g.f. is the ordinary one, Sum_{n>=1} a(n) x^n, stated as an identity of formal power series
  over `ℚ` with the denominator `(1 - 16x)(1 - 144x)` cleared (it has constant coefficient 1, so
  it is invertible). The coefficient of x^0 is 0 since the sequence starts at n = 1.
* The formula is stated in `ℚ` for every n ≥ 1 (there `4 * n - 3` is the natural number 4n - 3,
  and the division by 9 is exact).
-/

namespace OMA.S_oeis_a233252

open PowerSeries

/-- Two entries clash when they are equal or sum to 5 (the second is 5 minus the first). -/
def Clash (u v : Fin 6) : Prop := u = v ∨ u.val + v.val = 5

/-- In row-major order, the cell `(i', j')` comes before the cell `(i, j)`. -/
def Before {n : ℕ} (i' : Fin n) (j' : Fin 4) (i : Fin n) (j : Fin 4) : Prop :=
  i' < i ∨ (i' = i ∧ j' < j)

/-- The value `u` appears before the value `v` in row-major order: every cell with value `v`
comes after some cell with value `u` (vacuous when `v` does not appear). -/
def AppearsBefore {n : ℕ} (x : Fin n → Fin 4 → Fin 6) (u v : Fin 6) : Prop :=
  ∀ (i : Fin n) (j : Fin 4), x i j = v → ∃ (i' : Fin n) (j' : Fin 4), Before i' j' i j ∧ x i' j' = u

/-- The conditions of the definition on an n X 4 array `x` with entries in 0..5: no clash
between horizontal neighbours `(i, j)`, `(i, j + 1)` or antidiagonal neighbours `(i, j + 1)`,
`(i + 1, j)`; top left entry 0; 1 appearing before 2, 3 and 4; 2 appearing before 3. -/
def Good {n : ℕ} (x : Fin n → Fin 4 → Fin 6) : Prop :=
  (∀ (i : Fin n) (j : Fin 4) (hj : j.val + 1 < 4), ¬ Clash (x i j) (x i ⟨j.val + 1, hj⟩)) ∧
  (∀ (i : Fin n) (j : Fin 4) (hi : i.val + 1 < n) (hj : j.val + 1 < 4),
    ¬ Clash (x i ⟨j.val + 1, hj⟩) (x ⟨i.val + 1, hi⟩ j)) ∧
  (∀ h : 0 < n, x ⟨0, h⟩ 0 = 0) ∧
  AppearsBefore x 1 2 ∧ AppearsBefore x 1 3 ∧ AppearsBefore x 1 4 ∧
  AppearsBefore x 2 3

/-- A233252(n): the number of n X 4 0..5 arrays satisfying `Good`. -/
noncomputable def a (n : ℕ) : ℕ := Nat.card {x : Fin n → Fin 4 → Fin 6 // Good x}

/-- Barker's conjectures: the generating function `2x(5 - 208x)/((1 - 16x)(1 - 144x))`, and
`a(n) = 2^(4n-3) (4 * 9^n + 9)/9` for `n ≥ 1`. -/
theorem main :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) *
        ((1 - 16 * X) * (1 - 144 * X)) = 2 * X * (5 - 208 * X) ∧
    (∀ n : ℕ, 1 ≤ n → (a n : ℚ) = 2 ^ (4 * n - 3) * (4 * 9 ^ n + 9) / 9) := by
  sorry

end OMA.S_oeis_a233252

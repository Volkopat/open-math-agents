import Mathlib

/-!
# A184540: Number of (n+2) X 3 binary arrays with each 3 X 3 subblock having rows and columns in lexicographically nondecreasing order.

Source: https://oeis.org/A184540
Credit: @Salofe

Conjectures from Colin Barker, Apr 12 2018, quoted verbatim from the entry:
* "G.f.: x*(45 - 91*x + 61*x^2 - 14*x^3) / (1 - x)^4."
* "a(n) = 4*a(n-1) - 6*a(n-2) + 4*a(n-3) - a(n-4) for n>4."

Formalization notes:
* Offset 1, as in the entry (data: 45, 89, 147, 220, 309, ...): `a n` counts the arrays with
  `n + 2` rows. The value `a 0` (arrays with 2 rows, which have no 3 X 3 subblock) is never used.
* An (n+2) X 3 binary array is a function `A : Fin (n + 2) → Fin 3 → Fin 2`; `A i j` is the
  entry in row `i` (top to bottom) and column `j` (left to right), with entries 0 < 1. Arrays are
  labelled: they are not identified up to symmetry.
* A 3 X 3 subblock is made of 3 consecutive rows and 3 consecutive columns (a contiguous
  subblock). The one whose top left entry is `A i j` has the entry `A (i + r) (j + c)` in its row
  `r` and column `c` (`r, c ∈ {0, 1, 2}`).
* "Rows in lexicographically nondecreasing order": the three rows of the subblock, each read left
  to right as a word, are lexicographically nondecreasing from top to bottom. "Columns in
  lexicographically nondecreasing order": the three columns of the subblock, each read top to
  bottom as a word, are lexicographically nondecreasing from left to right. `LexLE x y` is the
  lexicographic order on words of length 3 over {0, 1}: the first position where the words differ
  decides.
* This reading reproduces the data: exhaustive enumeration of all arrays gives 45, 89, 147, 220,
  309 for n = 1, ..., 5, and the seven 4 X 3 solutions shown in the entry satisfy it. Reading the
  columns bottom to top instead would give 20, 35, 56 for n = 1, 2, 3.
* The g.f. is the ordinary one, Sum_{n>=1} a(n) x^n, stated as an identity of formal power series
  over `ℚ` with the denominator `(1 - x)^4` cleared (it has constant coefficient 1, so it is
  invertible). The coefficient of x^0 is 0 since the sequence starts at n = 1.
* The recurrence is stated in `ℤ` for every n > 4, as in the entry.
-/

namespace OMA.S_oeis_a184540

/-- `LexLE x y`: the word `x` is lexicographically at most the word `y` (words of length 3 over
{0, 1}), that is, `x = y`, or `x` and `y` agree before some position `i` and `x i < y i`. -/
def LexLE (x y : Fin 3 → Fin 2) : Prop :=
  x = y ∨ ∃ i : Fin 3, (∀ j : Fin 3, j < i → x j = y j) ∧ x i < y i

/-- Every 3 X 3 subblock `B` of `A` (3 consecutive rows and 3 consecutive columns) has its rows,
each read left to right, in lexicographically nondecreasing order from top to bottom, and its
columns, each read top to bottom, in lexicographically nondecreasing order from left to right. -/
def Good {m k : ℕ} (A : Fin m → Fin k → Fin 2) : Prop :=
  ∀ (i j : ℕ) (hi : i + 2 < m) (hj : j + 2 < k),
    let B : Fin 3 → Fin 3 → Fin 2 := fun r c =>
      A ⟨i + r, by have := r.isLt; omega⟩ ⟨j + c, by have := c.isLt; omega⟩
    LexLE (B 0) (B 1) ∧ LexLE (B 1) (B 2) ∧
      LexLE (fun r => B r 0) (fun r => B r 1) ∧ LexLE (fun r => B r 1) (fun r => B r 2)

/-- A184540(n): the number of (n+2) X 3 binary arrays all of whose 3 X 3 subblocks have their
rows and columns in lexicographically nondecreasing order. -/
noncomputable def a (n : ℕ) : ℕ := by
  classical
  exact Fintype.card {A : Fin (n + 2) → Fin 3 → Fin 2 // Good A}

open PowerSeries in
/-- Barker's conjectures: the generating function `x(45 - 91x + 61x^2 - 14x^3)/(1 - x)^4`, and
the recurrence `a(n) = 4a(n-1) - 6a(n-2) + 4a(n-3) - a(n-4)` for `n > 4`. -/
theorem main :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) * (1 - X) ^ 4 =
        X * (45 - 91 * X + 61 * X ^ 2 - 14 * X ^ 3) ∧
    ∀ n : ℕ, 4 < n → (a n : ℤ) = 4 * a (n - 1) - 6 * a (n - 2) + 4 * a (n - 3) - a (n - 4) := by
  sorry

end OMA.S_oeis_a184540

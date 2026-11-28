import Mathlib

/-!
# A220035: minima over horizontal and diagonal neighbors of sorted 0..1 5 X n arrays

A220035(n) is the number of distinct 5 X n arrays `B` obtained as follows. Start from a
0..1 5 X n array `A` that is "sorted with lexicographically nondecreasing rows and
nonincreasing columns": reading each row left to right as a word, the rows are
lexicographically nondecreasing from top to bottom, and reading each column top to bottom
as a word, the columns are lexicographically nonincreasing from left to right. Then
`B i j` is the minimum of `A i j` and of its horizontal neighbors `(i, j ± 1)` and its
diagonal neighbors `(i - 1, j - 1)`, `(i + 1, j + 1)` that lie inside the array.

Reading of the definition (the OEIS name is terse): "diagonal" is the main-diagonal
direction (antidiagonal neighbors `(i - 1, j + 1)`, `(i + 1, j - 1)` are used by sibling
sequences such as A219853). With this reading a brute-force count gives
6, 10, 21, 55, 111, 192, 302 for n = 1..7, matching the listed terms; the antidiagonal
reading gives 6, 6, 20, 50, 105, which does not.

Entries are `Bool` with `false < true` (0 < 1); the minimum of 0..1 values is 1 exactly
when all of them are 1.

The offset is 1; `a 0` (the count of empty 5 X 0 arrays) is not a term of the sequence
and is set to 0 in the generating function, which has no constant term.

The problem: the conjectures of Colin Barker (Jul 30 2018):
  G.f.: x*(6 - 20*x + 31*x^2 - 10*x^3 - 24*x^4 + 21*x^5 - 3*x^6 - 4*x^7 + 8*x^8 - 3*x^9
        - x^10) / (1 - x)^5,
  a(n) = 5*a(n-1) - 10*a(n-2) + 10*a(n-3) - 5*a(n-4) + a(n-5) for n > 11.
The g.f. is stated after multiplying both sides by (1 - x)^5. (R. H. Hardin's empirical
polynomial for n > 6 follows from the g.f.)

Source: https://oeis.org/A220035
Credit: @VashaTS
-/

namespace OMA.S_oeis_a220035

open PowerSeries

/-- A 0..1 array with 5 rows and `n` columns: `A i j` is the entry in row `i`, column `j`. -/
abbrev Grid (n : ℕ) := Fin 5 → Fin n → Bool

/-- Row `i` read left to right. -/
def row {n : ℕ} (A : Grid n) (i : Fin 5) : List Bool := List.ofFn (A i)

/-- Column `j` read top to bottom. -/
def col {n : ℕ} (A : Grid n) (j : Fin n) : List Bool := List.ofFn fun i => A i j

/-- Rows lexicographically nondecreasing top to bottom, columns lexicographically
nonincreasing left to right. -/
def IsSorted {n : ℕ} (A : Grid n) : Prop :=
  (∀ i i' : Fin 5, i ≤ i' → row A i ≤ row A i') ∧
    ∀ j j' : Fin n, j ≤ j' → col A j' ≤ col A j

instance {n : ℕ} (A : Grid n) : Decidable (IsSorted A) := by
  unfold IsSorted; infer_instance

/-- Cell `(i', j')` is `(i, j)` itself, a horizontal neighbor `(i, j ± 1)`, or a diagonal
neighbor `(i - 1, j - 1)` or `(i + 1, j + 1)`. -/
def Near {n : ℕ} (i i' : Fin 5) (j j' : Fin n) : Prop :=
  (i' = i ∧ (j' = j ∨ j'.val + 1 = j.val ∨ j'.val = j.val + 1)) ∨
    (i'.val + 1 = i.val ∧ j'.val + 1 = j.val) ∨
    (i'.val = i.val + 1 ∧ j'.val = j.val + 1)

instance {n : ℕ} (i i' : Fin 5) (j j' : Fin n) : Decidable (Near i i' j j') := by
  unfold Near; infer_instance

/-- The array of minima of each cell and its horizontal and diagonal neighbors. -/
def minArray {n : ℕ} (A : Grid n) : Grid n :=
  fun i j => decide (∀ i' : Fin 5, ∀ j' : Fin n, Near i i' j j' → A i' j' = true)

/-- The number of distinct arrays of minima over all sorted 0..1 5 X n arrays. -/
def a (n : ℕ) : ℕ :=
  ((Finset.univ.filter fun A : Grid n => IsSorted A).image minArray).card

theorem main :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) * (1 - X) ^ 5 =
      X * (6 - 20 * X + 31 * X ^ 2 - 10 * X ^ 3 - 24 * X ^ 4 + 21 * X ^ 5 - 3 * X ^ 6
        - 4 * X ^ 7 + 8 * X ^ 8 - 3 * X ^ 9 - X ^ 10) ∧
    ∀ n : ℕ, 11 < n →
      (a n : ℤ) = 5 * a (n - 1) - 10 * a (n - 2) + 10 * a (n - 3) - 5 * a (n - 4) + a (n - 5) := by
  sorry

end OMA.S_oeis_a220035

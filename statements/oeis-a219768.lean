import Mathlib

/-!
# A219768: Number of n X 3 arrays of the minimum value of corresponding elements and their horizontal or antidiagonal neighbors in a random, but sorted with lexicographically nondecreasing rows and columns, 0..1 n X 3 array.

Source: https://oeis.org/A219768
Credit: @Salofe

The sequence is due to R. H. Hardin (Nov 27 2012); it is column 3 of A219773.

Conjectures from Colin Barker, Jul 27 2018, quoted verbatim from the entry:
* "G.f.: x*(1 - 2*x + 2*x^2)*(3 - 3*x + 2*x^2 - x^3) / (1 - x)^5."
* "a(n) = 5*a(n-1) - 10*a(n-2) + 10*a(n-3) - 5*a(n-4) + a(n-5) for n>6."

The entry also lists Hardin's "Empirical: a(n) = (1/24)*n^4 + (1/4)*n^3 - (25/24)*n^2 +
(23/4)*n - 4 for n>1."; that closed form is not part of this statement, which states Barker's
two conjectures only.

Formalization notes:
* Offset 1, as in the entry (data: 3, 6, 14, 29, 56, 101, 171, 274, 419, ...). The value `a 0`
  (it counts the empty array once) is never used: the g.f. has coefficient 0 at x^0, and the
  recurrence (n > 6) only involves a(n-5), ..., a(n) with n - 5 ≥ 2.
* An n X 3 0..1 array is a function `A : Fin n → Fin 3 → Fin 2`; `A i j` is the entry in row `i`
  (rows numbered from top to bottom) and column `j` (columns numbered from left to right), with
  the usual order 0 < 1 on entries. Arrays are labelled: they are not identified up to symmetry.
* "Sorted with lexicographically nondecreasing rows and columns": the rows, each read left to
  right, are lexicographically nondecreasing from top to bottom,
  `Monotone (fun i => toLex (A i))`, and the columns, each read top to bottom, are
  lexicographically nondecreasing from left to right, `Monotone (fun j => toLex (fun i => A i j))`.
  `toLex` gives the words Mathlib's order `Pi.Lex`, in which the first position where two words
  differ decides.
* Neighbours: the cell `(i', j')` is taken into account at the cell `(i, j)` when the offset
  `(i' - i, j' - j)` is `(0, 0)` (the element itself), `(0, 1)` or `(0, -1)` (its horizontal
  neighbours), or `(-1, 1)` or `(1, -1)` (its antidiagonal neighbours, up-right and down-left);
  only cells inside the array count (`IsNbr`). The resulting array has at `(i, j)` the minimum of
  the entries of `A` at these cells (`minNbr`; the set always contains `(i, j)` itself, so the
  infimum is this minimum).
* `a n` is the number of distinct resulting arrays, over all sorted n X 3 0..1 arrays `A`.
* This reading reproduces the data: exhaustive enumeration gives 3, 6, 14, 29, 56, 101, 171 for
  n = 1, ..., 7; an automaton count of the same definition gives all 210 terms of the b-file
  (n = 1..210); all seven example arrays of the entry (n = 3) are resulting arrays; and the same
  definition for n X 1, n X 2 and n X 4 arrays gives 2, 3, 4, 5, 6, 7 and 2, 4, 6, 8, 10, 12 and
  4, 9, 33, 100, columns 1, 2 and 4 of A219773. Taking the diagonal neighbours `(-1, -1)`,
  `(1, 1)` instead of the antidiagonal ones would give 3, 6, 14, 30, ... instead, and
  lexicographically nonincreasing columns would give 3, 5, 9, ... .
* The g.f. is the ordinary one, Sum_{n>=1} a(n) x^n, stated as an identity of formal power series
  over `ℚ` with the denominator `(1 - x)^5` cleared (it has constant coefficient 1, so it is
  invertible); the numerator is kept in the factored form of the entry. The coefficient of x^0 is
  0 since the sequence starts at n = 1.
* The recurrence is stated in `ℤ` for every n > 6, as in the entry.
-/

namespace OMA.S_oeis_a219768

/-- The rows of `A`, read left to right, are lexicographically nondecreasing from top to bottom,
and the columns of `A`, read top to bottom, are lexicographically nondecreasing from left to
right. -/
def Sorted {n : ℕ} (A : Fin n → Fin 3 → Fin 2) : Prop :=
  Monotone (fun i => toLex (A i)) ∧ Monotone (fun j => toLex (fun i => A i j))

/-- The cell `q` is the cell `p` itself or one of its horizontal or antidiagonal neighbours: the
offset from `p` to `q` (row offset, column offset) is `(0, 0)`, `(0, 1)`, `(0, -1)`, `(-1, 1)` or
`(1, -1)`. -/
def IsNbr {n : ℕ} (p q : Fin n × Fin 3) : Prop :=
  ((q.1 : ℤ) - p.1, (q.2 : ℤ) - p.2) ∈
    ({(0, 0), (0, 1), (0, -1), (-1, 1), (1, -1)} : Finset (ℤ × ℤ))

/-- The minimum of the entries of `A` at the cell `p` and at its horizontal and antidiagonal
neighbours inside the array. -/
noncomputable def minNbr {n : ℕ} (A : Fin n → Fin 3 → Fin 2) (p : Fin n × Fin 3) : Fin 2 := by
  classical
  exact (Finset.univ.filter (fun q => IsNbr p q)).inf (fun q => A q.1 q.2)

/-- A219768(n): the number of distinct n X 3 arrays `fun i j => minNbr A (i, j)` of minimum
values, over all sorted n X 3 arrays `A` with entries in 0..1. -/
noncomputable def a (n : ℕ) : ℕ := by
  classical
  exact ((Finset.univ.filter (fun A : Fin n → Fin 3 → Fin 2 => Sorted A)).image
    (fun A => fun i j => minNbr A (i, j))).card

open PowerSeries in
/-- Barker's conjectures: the generating function
`x(1 - 2x + 2x^2)(3 - 3x + 2x^2 - x^3)/(1 - x)^5`, and the recurrence
`a(n) = 5a(n-1) - 10a(n-2) + 10a(n-3) - 5a(n-4) + a(n-5)` for `n > 6`. -/
theorem main :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) * (1 - X) ^ 5 =
        X * (1 - 2 * X + 2 * X ^ 2) * (3 - 3 * X + 2 * X ^ 2 - X ^ 3) ∧
    (∀ n : ℕ, 6 < n → (a n : ℤ) = 5 * a (n - 1) - 10 * a (n - 2) + 10 * a (n - 3) -
      5 * a (n - 4) + a (n - 5)) := by
  sorry

end OMA.S_oeis_a219768

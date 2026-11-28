import Mathlib

/-!
# A201695: Number of n X 3 0..2 arrays with rows and columns lexicographically nondecreasing read forwards and nonincreasing read backwards.

Source: https://oeis.org/A201695
Credit: @Salofe

Conjectures from the entry, quoted verbatim:
* Colin Barker, May 23 2018: "G.f.: x*(3 + 3*x + 56*x^2 - 35*x^3 + 9*x^4) / (1 - x)^5." and
  "a(n) = 5*a(n-1) - 10*a(n-2) + 10*a(n-3) - 5*a(n-4) + a(n-5) for n>5."
* R. H. Hardin, in the entry he created (Dec 03 2011): "Empirical: a(n) = (3/2)*n^4
  + (4/3)*n^3 - 4*n^2 - (29/6)*n + 9."

Formalization notes:
* Offset 1, as in the entry (data: 3, 18, 116, 395, 989, 2068, ...). The value `a 0` (the empty
  array, counted once) is never used: every claim below is about n ≥ 1 only.
* An n X 3 0..2 array is a function `A : Fin n → Fin 3 → Fin 3`; `A i j` is the entry in row `i`
  (top to bottom) and column `j` (left to right), with the usual order 0 < 1 < 2 on entries.
  Arrays are labelled: they are not identified up to symmetry.
* Rows and columns are compared as words in the lexicographic order: `toLex` gives the words
  Mathlib's order `Pi.Lex`, in which the first position where two words differ decides.
* "Rows lexicographically nondecreasing read forwards": the rows, each read left to right, are
  lexicographically nondecreasing from top to bottom, `Monotone (fun i => toLex (A i))`.
  "Rows lexicographically nonincreasing read backwards": the rows, each read right to left, are
  lexicographically nonincreasing from top to bottom,
  `Antitone (fun i => toLex (fun j => A i (Fin.rev j)))` (`Fin.rev j = 2 - j`).
* "Columns lexicographically nondecreasing read forwards": the columns, each read top to bottom,
  are lexicographically nondecreasing from left to right,
  `Monotone (fun j => toLex (fun i => A i j))`. "Columns lexicographically nonincreasing read
  backwards": the columns, each read bottom to top, are lexicographically nonincreasing from
  left to right, `Antitone (fun j => toLex (fun i => A (Fin.rev i) j))`.
* This reading reproduces the data: exhaustive enumeration gives 3, 18, 116, 395, 989, 2068,
  3838, 6541, 10455, 15894 for n = 1, ..., 10, a transfer-matrix count based on it agrees with the
  whole b-file (n = 1, ..., 210), and all seven 4 X 3 solutions shown in the entry satisfy it. For
  n = 1 the columns are single entries x, y, z, and the conditions force x ≤ y ≤ z and
  x ≥ y ≥ z, hence a(1) = 3. Reading "backwards" as running through the rows (resp. columns) in
  the opposite order would make each "backwards" condition a restatement of the "forwards" one,
  and would give a(1) = 10.
* The g.f. is the ordinary one, Sum_{n>=1} a(n) x^n, stated as an identity of formal power series
  over `ℚ` with the denominator `(1 - x)^5` cleared (it has constant coefficient 1, so it is
  invertible). The coefficient of x^0 is 0 since the sequence starts at n = 1.
* The recurrence is stated in `ℤ` for every n > 5, as in the entry.
* Hardin's empirical formula is stated in `ℚ` for every n ≥ 1, the indices of the sequence.
-/

namespace OMA.S_oeis_a201695

/-- The rows of `A`, read left to right, are lexicographically nondecreasing from top to bottom,
and read right to left, lexicographically nonincreasing from top to bottom; the columns of `A`,
read top to bottom, are lexicographically nondecreasing from left to right, and read bottom to
top, lexicographically nonincreasing from left to right. -/
def Good {n : ℕ} (A : Fin n → Fin 3 → Fin 3) : Prop :=
  Monotone (fun i => toLex (A i)) ∧ Antitone (fun i => toLex (fun j => A i (Fin.rev j))) ∧
    Monotone (fun j => toLex (fun i => A i j)) ∧
    Antitone (fun j => toLex (fun i => A (Fin.rev i) j))

/-- A201695(n): the number of n X 3 arrays with entries in {0, 1, 2} whose rows and columns are
lexicographically nondecreasing read forwards and nonincreasing read backwards. -/
noncomputable def a (n : ℕ) : ℕ := by
  classical
  exact Fintype.card {A : Fin n → Fin 3 → Fin 3 // Good A}

open PowerSeries in
/-- Barker's conjectures: the generating function
`x(3 + 3x + 56x^2 - 35x^3 + 9x^4)/(1 - x)^5`, and the recurrence
`a(n) = 5a(n-1) - 10a(n-2) + 10a(n-3) - 5a(n-4) + a(n-5)` for `n > 5`; and Hardin's empirical
formula `a(n) = (3/2)n^4 + (4/3)n^3 - 4n^2 - (29/6)n + 9` for `n ≥ 1`. -/
theorem main :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) * (1 - X) ^ 5 =
        X * (3 + 3 * X + 56 * X ^ 2 - 35 * X ^ 3 + 9 * X ^ 4) ∧
    (∀ n : ℕ, 5 < n → (a n : ℤ) = 5 * a (n - 1) - 10 * a (n - 2) + 10 * a (n - 3) -
      5 * a (n - 4) + a (n - 5)) ∧
    (∀ n : ℕ, 1 ≤ n → (a n : ℚ) = (3 / 2) * (n : ℚ) ^ 4 + (4 / 3) * (n : ℚ) ^ 3
      - 4 * (n : ℚ) ^ 2 - (29 / 6) * (n : ℚ) + 9) := by
  sorry

end OMA.S_oeis_a201695

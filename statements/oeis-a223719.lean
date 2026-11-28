import Mathlib

/-!
# A223719: Number of n X 2 0..2 arrays with rows, antidiagonals and columns unimodal.

Source: https://oeis.org/A223719
Credit: @Salofe

The sequence is due to R. H. Hardin (Mar 26 2013); it is column 2 of A223725.

Conjectures from Colin Barker, Feb 19 2018, quoted verbatim from the entry:
* "G.f.: x*(9 + 79*x^2 - 80*x^3 + 106*x^4 - 68*x^5 + 31*x^6 - 8*x^7 + x^8) / (1 - x)^9."
* "a(n) = 9*a(n-1) - 36*a(n-2) + 84*a(n-3) - 126*a(n-4) + 126*a(n-5) - 84*a(n-6) +
  36*a(n-7) - 9*a(n-8) + a(n-9) for n>9."

The entry also lists Hardin's "Empirical: a(n) = (1/576)*n^8 + (1/48)*n^7 + (41/288)*n^6 +
(13/24)*n^5 + (793/576)*n^4 + (31/16)*n^3 + (119/48)*n^2 + (3/2)*n + 1."; that closed form is
not part of this statement, which states Barker's two conjectures only.

Formalization notes:
* Offset 1, as in the entry (data: 9, 81, 484, 2116, 7396, 21904, 57121, ...). The value `a 0`
  is never used: the g.f. has coefficient 0 at x^0, and the recurrence (n > 9) only involves
  a(n-9), ..., a(n) with n - 9 ≥ 1. (With the definitions below `a 0 = 1`, the empty array.)
* An n X 2 0..2 array is a function `A : Fin n → Fin 2 → Fin 3`; `A i j` is the entry in row `i`
  (rows numbered from top to bottom) and column `j` (columns numbered from left to right), with
  the order 0 < 1 < 2 on entries. Arrays are labelled: they are not identified up to symmetry.
* A list is unimodal (`Unimodal`) when it is weakly increasing up to some point and weakly
  decreasing from there on: it splits as `l₁ ++ l₂` with `l₁` nondecreasing
  (`List.Pairwise (· ≤ ·)`) and `l₂` nonincreasing (`List.Pairwise (· ≥ ·)`); either part may
  be empty. A list is unimodal if and only if its reverse is, so the direction in which a line
  of the array is read does not matter.
* Rows are read left to right (`List.ofFn (A i)`) and columns top to bottom
  (`List.ofFn fun i => A i j`). The antidiagonal number `d` (`antidiag A d`) is the list of the
  entries `A i j` with `i + j = d`, read from the top: row `i` increasing, column `j = d - i`
  decreasing, i.e. from the upper right end of the antidiagonal to its lower left end. The
  condition is required for every `d : ℕ`; for `d ≥ n + 1` the list is empty, which is unimodal,
  so this is the same as requiring it for the `n + 1` antidiagonals of the array (the corner
  cells `d = 0` and `d = n` included).
* "Rows, antidiagonals and columns unimodal": every row, every antidiagonal and every column of
  `A` is unimodal (`Good`), and `a n` is the number of such n X 2 arrays.
* This reading reproduces the data: an exhaustive enumeration of all n X 2 arrays over 0..2,
  computing exactly the definitions below, gives 9, 81, 484, 2116, 7396, 21904 for
  n = 1, ..., 6, and the ten 3 X 2 example arrays shown in the entry all satisfy `Good`. (The
  same enumeration for n X 1 arrays gives 3, 9, 22, 46, 86, 148, 239, 367, column 1 of A223725.)
  With these definitions a(n) = u(n)^2, where u(n) = C(n+3,4) + C(n+1,2) + 1 is the number of
  unimodal words of length n over 0..2 (only the two columns are constrained); this agrees with
  all 210 terms of the b-file (n = 1..210).
* The g.f. is the ordinary one, Sum_{n>=1} a(n) x^n, stated as an identity of formal power series
  over `ℚ` with the denominator `(1 - x)^9` cleared (it has constant coefficient 1, so it is
  invertible). The coefficient of x^0 is 0 since the sequence starts at n = 1.
* The recurrence is stated in `ℤ` for every n > 9, as in the entry.
-/

namespace OMA.S_oeis_a223719

open PowerSeries

/-- A list is unimodal: it is weakly increasing up to some point and weakly decreasing from there
on (either part may be empty). -/
def Unimodal (l : List (Fin 3)) : Prop :=
  ∃ l₁ l₂ : List (Fin 3), l = l₁ ++ l₂ ∧ l₁.Pairwise (· ≤ ·) ∧ l₂.Pairwise (· ≥ ·)

/-- The antidiagonal number `d` of the R X C array `A` (`A i j` is the entry in row `i` and
column `j`): the entries `A i j` with `i + j = d`, read from the top (row `i` increasing, column
`j = d - i` decreasing). -/
def antidiag {R C : ℕ} (A : Fin R → Fin C → Fin 3) (d : ℕ) : List (Fin 3) :=
  (List.finRange R).filterMap fun i : Fin R =>
    if h : (i : ℕ) ≤ d ∧ d - i < C then some (A i ⟨d - i, h.2⟩) else none

/-- Every row (read left to right), every antidiagonal (read from the top) and every column (read
top to bottom) of the n X 2 array `A` is unimodal; `A i j` is the entry in row `i` and column
`j`. -/
def Good {n : ℕ} (A : Fin n → Fin 2 → Fin 3) : Prop :=
  (∀ i, Unimodal (List.ofFn (A i))) ∧
  (∀ d, Unimodal (antidiag A d)) ∧
  (∀ j, Unimodal (List.ofFn fun i => A i j))

/-- A223719(n): the number of n X 2 0..2 arrays with rows, antidiagonals and columns
unimodal. -/
noncomputable def a (n : ℕ) : ℕ := Nat.card {A : Fin n → Fin 2 → Fin 3 // Good A}

/-- Barker's conjectures: the generating function
`x(9 + 79x^2 - 80x^3 + 106x^4 - 68x^5 + 31x^6 - 8x^7 + x^8)/(1 - x)^9`, and the recurrence
`a(n) = 9a(n-1) - 36a(n-2) + 84a(n-3) - 126a(n-4) + 126a(n-5) - 84a(n-6) + 36a(n-7) - 9a(n-8) +
a(n-9)` for `n > 9`. -/
theorem main :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) * (1 - X) ^ 9 =
        X * (9 + 79 * X ^ 2 - 80 * X ^ 3 + 106 * X ^ 4 - 68 * X ^ 5 + 31 * X ^ 6 - 8 * X ^ 7 +
          X ^ 8) ∧
    (∀ n : ℕ, 9 < n → (a n : ℤ) = 9 * a (n - 1) - 36 * a (n - 2) + 84 * a (n - 3) -
      126 * a (n - 4) + 126 * a (n - 5) - 84 * a (n - 6) + 36 * a (n - 7) - 9 * a (n - 8) +
      a (n - 9)) := by
  sorry

end OMA.S_oeis_a223719

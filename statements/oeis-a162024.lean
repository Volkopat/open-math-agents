import Mathlib

/-!
# A162024: Number of n X n binary arrays with rows and columns, considered as binary numbers, in nondecreasing order, and all but the outermost row or column zero.

Source: https://oeis.org/A162024
Credit: @Salofe

Conjectures from Colin Barker, Mar 24 2018, quoted verbatim from the entry:
* "G.f.: x^2*(7 - x + x^2 + x^3) / (1 - x)^3."
* "a(n) = 4*(2 - 2*n + n^2) for n>2."

Formalization notes:
* Offset 2, as in the entry (data: 7, 20, 40, 68, 104, 148, 200, ...). The g.f. is the series
  Sum_{n >= 2} a(n) x^n, so its coefficients of x^0 and x^1 are 0. The values `a 0 = 1` (the empty
  array) and `a 1 = 2` (the two 1 X 1 arrays) of the definition below are never used.
* An n X n binary array is `A : Fin n → Fin n → Fin 2`; `A i j` is the entry in row `i` (rows
  numbered 0, ..., n-1 from the top) and column `j` (columns numbered 0, ..., n-1 from the left).
* Rows and columns considered as binary numbers: row `i` is the number
  `Σ_j A i j * 2^(n-1-j)` (its leftmost entry is the most significant bit) and column `j` is the
  number `Σ_i A i j * 2^(n-1-i)` (its top entry is the most significant bit).
* In nondecreasing order: the row numbers are nondecreasing from the top row to the bottom row,
  and the column numbers are nondecreasing from the left column to the right column (`Monotone`
  on `Fin n`).
* All but the outermost row or column zero: every entry that lies neither in the first or last
  row nor in the first or last column is 0, i.e. `A i j = 0` whenever `0 < i < n-1` and
  `0 < j < n-1`. (Allowing nonzero entries only in the last row and column, or only in the
  first row and column, does not reproduce the data under any of the 16 conventions below.)
* Conventions: of the 16 ways to choose the bit order of the rows, the bit order of the columns,
  and the direction of each of the two orders, exactly 4 reproduce the data 7, 20, 40, 68, 104
  for n = 2..6: the one used here and its images under reflecting the array left-right, up-down,
  or both. A reflection is a bijection between the arrays counted under the two conventions, so
  these 4 give the same sequence.
* The g.f. is stated as an identity of formal power series over `ℚ` with the denominator cleared,
  `A(x) * (1 - x)^3 = x^2 * (7 - x + x^2 + x^3)`; this is equivalent to the g.f. because
  `(1 - x)^3` has constant term 1, so it is invertible.
* The closed form is stated in `ℤ` for every n > 2, as in the entry.
-/

namespace OMA.S_oeis_a162024

/-- Row `i` of the array `A`, read as a binary number whose most significant bit is the leftmost
entry `A i 0`. -/
def rowVal {n : ℕ} (A : Fin n → Fin n → Fin 2) (i : Fin n) : ℕ :=
  ∑ j : Fin n, (A i j : ℕ) * 2 ^ (n - 1 - (j : ℕ))

/-- Column `j` of the array `A`, read as a binary number whose most significant bit is the top
entry `A 0 j`. -/
def colVal {n : ℕ} (A : Fin n → Fin n → Fin 2) (j : Fin n) : ℕ :=
  ∑ i : Fin n, (A i j : ℕ) * 2 ^ (n - 1 - (i : ℕ))

/-- The arrays counted by A162024: the rows (as binary numbers) are nondecreasing from top to
bottom, the columns (as binary numbers) are nondecreasing from left to right, and every entry
outside the outermost rows and columns is zero. -/
def Good {n : ℕ} (A : Fin n → Fin n → Fin 2) : Prop :=
  Monotone (rowVal A) ∧ Monotone (colVal A) ∧
    ∀ i j : Fin n, 0 < (i : ℕ) → (i : ℕ) < n - 1 → 0 < (j : ℕ) → (j : ℕ) < n - 1 → A i j = 0

/-- A162024(n): the number of `n × n` binary arrays with the properties of `Good`. -/
noncomputable def a (n : ℕ) : ℕ := by
  classical
  exact Fintype.card {A : Fin n → Fin n → Fin 2 // Good A}

open PowerSeries in
/-- Barker's conjectures: the g.f. `x^2 (7 - x + x^2 + x^3) / (1 - x)^3` (offset 2), and
`a(n) = 4 (2 - 2n + n^2)` for `n > 2`. -/
theorem main :
    PowerSeries.mk (fun n => if n < 2 then (0 : ℚ) else (a n : ℚ)) * (1 - X) ^ 3 =
        X ^ 2 * (7 - X + X ^ 2 + X ^ 3) ∧
    ∀ n : ℕ, 2 < n → (a n : ℤ) = 4 * (2 - 2 * n + n ^ 2) := by
  sorry

end OMA.S_oeis_a162024

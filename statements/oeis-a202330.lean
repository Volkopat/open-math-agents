import Mathlib

/-!
# A202330: Number of (n+1) X 4 binary arrays with consecutive windows of two bits considered as a binary number nondecreasing in every row and column.

Source: https://oeis.org/A202330
Credit: @Salofe

Conjectures from Colin Barker, May 27 2018, quoted verbatim from the entry (by R. H. Hardin,
Dec 17 2011):
"Conjectures from Colin Barker, May 27 2018: (Start)
G.f.: x*(36 - 98*x + 112*x^2 - 61*x^3 + 13*x^4) / (1 - x)^5.
a(n) = 5*a(n-1) - 10*a(n-2) + 10*a(n-3) - 5*a(n-4) + a(n-5).
(End)"

Formalization notes:
* Offset 1, as in the entry (data: 36, 82, 162, 289, 478, ...): `a n` counts the arrays with
  `n + 1` rows and 4 columns. The value `a 0` (arrays with a single row) is never used.
* An (n+1) X 4 binary array is a function `A : Fin (n + 1) → Fin 4 → Bool`; `A i j` is the
  entry in row `i` (top to bottom) and column `j` (left to right), with `false` = 0 and
  `true` = 1. Arrays are labelled: they are not identified up to symmetry.
* A row is read left to right and a column top to bottom, as a word `b 0, b 1, ..., b (L - 1)`
  (`L = 4` for a row, `L = n + 1` for a column). Its consecutive windows of two bits are the
  overlapping pairs `(b i, b (i + 1))`, `i + 1 < L`, and the window `(b i, b (i + 1))` considered
  as a binary number is `win (b i) (b (i + 1)) = 2 * b i + b (i + 1)`: the first bit read is the
  high bit. "Nondecreasing" means that each window is at most the next one:
  `win (b i) (b (i + 1)) ≤ win (b (i + 1)) (b (i + 2))` for every `i` with `i + 2 < L`
  (`WindowsMono`). A word with fewer than 3 bits has no such condition.
* This reading reproduces the data: a brute-force evaluation of this definition gives 36, 82,
  162, 289, 478, 746, 1112 for n = 1, ..., 7, as in the data, a transfer-matrix evaluation of the
  same definition agrees with all 210 terms of the entry's b-file (n = 1..210), and the five
  6 X 4 solutions shown in the entry for n = 5 satisfy it. The examples fix the bit order and
  the directions: their row 0010 (windows 0, 1, 2) and their column 0, 0, 0, 0, 1, 0 (windows
  0, 0, 0, 1, 2) are nondecreasing only when the first bit read is the high bit, rows being read
  left to right and columns top to bottom. (With non-overlapping windows, a(1) would be 100
  instead of 36.)
* The g.f. is the ordinary one, Sum_{n>=1} a(n) x^n, stated as an identity of formal power
  series over `ℚ` with the denominator `(1 - x)^5` cleared (it has constant coefficient 1, so it
  is invertible). The coefficient of x^0 is 0 since the sequence starts at n = 1.
* The entry gives no range for the recurrence. It is stated in `ℤ` for every n > 5: these are
  the n for which all the indices n - 1, ..., n - 5 are in the range n >= 1 of the sequence.
-/

namespace OMA.S_oeis_a202330

/-- The window of two bits `(x, y)` considered as a binary number, `x` being the high bit:
`win x y = 2 x + y`, a number in `0..3`. -/
def win (x y : Bool) : ℕ := 2 * x.toNat + y.toNat

/-- The consecutive windows of two bits of the word `v 0, v 1, ..., v (L - 1)`, each considered as
a binary number, are nondecreasing: the window at positions `i, i + 1` is at most the window at
positions `i + 1, i + 2`, for every `i` with `i + 2 < L`. -/
def WindowsMono {L : ℕ} (v : Fin L → Bool) : Prop :=
  ∀ (i : ℕ) (h : i + 2 < L),
    win (v ⟨i, by omega⟩) (v ⟨i + 1, by omega⟩) ≤ win (v ⟨i + 1, by omega⟩) (v ⟨i + 2, h⟩)

/-- Every row of `A` (read left to right) and every column of `A` (read top to bottom) has its
consecutive windows of two bits, considered as binary numbers, nondecreasing. -/
def Good {m : ℕ} (A : Fin m → Fin 4 → Bool) : Prop :=
  (∀ i : Fin m, WindowsMono (A i)) ∧ (∀ j : Fin 4, WindowsMono (fun i : Fin m => A i j))

/-- A202330(n): the number of (n+1) X 4 binary arrays with consecutive windows of two bits
considered as a binary number nondecreasing in every row and column. -/
noncomputable def a (n : ℕ) : ℕ := Nat.card {A : Fin (n + 1) → Fin 4 → Bool // Good A}

open PowerSeries in
/-- Barker's conjectures: the generating function `x(36 - 98x + 112x^2 - 61x^3 + 13x^4)/(1 - x)^5`,
and the recurrence `a(n) = 5a(n-1) - 10a(n-2) + 10a(n-3) - 5a(n-4) + a(n-5)` for `n > 5`. -/
theorem main :
    PowerSeries.mk (fun n => if n < 1 then 0 else (a n : ℚ)) * ((1 - X) ^ 5 : PowerSeries ℚ) =
        X * (36 - 98 * X + 112 * X ^ 2 - 61 * X ^ 3 + 13 * X ^ 4) ∧
    ∀ n : ℕ, 5 < n →
      (a n : ℤ) = 5 * a (n - 1) - 10 * a (n - 2) + 10 * a (n - 3) - 5 * a (n - 4) + a (n - 5) := by
  sorry

end OMA.S_oeis_a202330

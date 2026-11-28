import Mathlib

/-!
# A224258: Number of n X 4 0..2 arrays with rows, diagonals and antidiagonals unimodal and columns nondecreasing.

Source: https://oeis.org/A224258
Credit: @prathameshnium (agent: Claude Code, model claude-opus-5-5)

The entry (R. H. Hardin, Apr 02 2013; column 4 of A224262; DATA 46, 548, 3096, 12467, 41012, ...) records in its FORMULA section:

  Empirical: a(n) = (41/4032)*n^8 + (9/112)*n^7 + (349/480)*n^6 + (69/20)*n^5 + (1325/192)*n^4 + (1571/48)*n^3 + (87503/5040)*n^2 - (21949/420)*n + 43 for n>2.
  Conjectures from Colin Barker, Aug 29 2018:
  G.f.: x*(46 + 134*x - 180*x^2 + 467*x^3 + 29*x^4 - 416*x^5 + 534*x^6 - 255*x^7 + 61*x^8 - 12*x^9 + 2*x^10) / (1 - x)^9.
  a(n) = 9*a(n-1) - 36*a(n-2) + 84*a(n-3) - 126*a(n-4) + 126*a(n-5) - 84*a(n-6) + 36*a(n-7) - 9*a(n-8) + a(n-9) for n>11.

Conventions:
* Offset 1. An `n X 4` array with entries 0..2 is `x : Fin n → Fin 4 → Fin 3`, where `x i j` is
  the entry in row `i` and column `j`. `a n` counts such arrays for every `n`; the conjectures concern `n ≥ 1`.
* A finite sequence is unimodal when it is weakly increasing and then weakly decreasing. Equivalently, no
  entry is strictly smaller than both an earlier and a later entry of the sequence; the definitions below
  use this second form. Rows are read left to right and columns top to bottom.
* Columns are nondecreasing: entries do not decrease going down a column.
* A diagonal is the set of cells with `j - i` constant, an antidiagonal the set with `i + j` constant;
  both are read in order of increasing `i` (the direction does not matter for unimodality).
* Empirical formula: stated over ℚ for `n > 2`. G.f.: an identity of formal power series over ℚ,
  with coefficient 0 at `x^0` (offset 1). Recurrence: stated in ℤ for `n > 11`.

Numerical check: a Python copy of these definitions gives the DATA of the entry (46, 548, 3096, 12467, ...) by
brute force over all arrays for small `n`.
-/

namespace OMA.S_oeis_a224258

open PowerSeries

/-- Every row is unimodal. -/
def RowsUnimodal {n : ℕ} (x : Fin n → Fin 4 → Fin 3) : Prop :=
  ∀ i : Fin n, ∀ j1 j2 j3 : Fin 4, j1 < j2 → j2 < j3 → ¬ (x i j2 < x i j1 ∧ x i j2 < x i j3)

instance {n : ℕ} (x : Fin n → Fin 4 → Fin 3) : Decidable (RowsUnimodal x) := by
  unfold RowsUnimodal; infer_instance

/-- Every column is nondecreasing downwards. -/
def ColumnsNondecreasing {n : ℕ} (x : Fin n → Fin 4 → Fin 3) : Prop :=
  ∀ i1 i2 : Fin n, ∀ j : Fin 4, i1 ≤ i2 → x i1 j ≤ x i2 j

instance {n : ℕ} (x : Fin n → Fin 4 → Fin 3) : Decidable (ColumnsNondecreasing x) := by
  unfold ColumnsNondecreasing; infer_instance

/-- Every diagonal (cells with `j - i` constant, read by increasing `i`) is unimodal. -/
def DiagonalsUnimodal {n : ℕ} (x : Fin n → Fin 4 → Fin 3) : Prop :=
  ∀ i1 i2 i3 : Fin n, ∀ j1 j2 j3 : Fin 4, i1 < i2 → i2 < i3 → (j1 : ℕ) + i2 = j2 + i1 →
    (j2 : ℕ) + i3 = j3 + i2 → ¬ (x i2 j2 < x i1 j1 ∧ x i2 j2 < x i3 j3)

instance {n : ℕ} (x : Fin n → Fin 4 → Fin 3) : Decidable (DiagonalsUnimodal x) := by
  unfold DiagonalsUnimodal; infer_instance

/-- Every antidiagonal (cells with `i + j` constant, read by increasing `i`) is unimodal. -/
def AntidiagonalsUnimodal {n : ℕ} (x : Fin n → Fin 4 → Fin 3) : Prop :=
  ∀ i1 i2 i3 : Fin n, ∀ j1 j2 j3 : Fin 4, i1 < i2 → i2 < i3 → (i1 : ℕ) + j1 = i2 + j2 →
    (i2 : ℕ) + j2 = i3 + j3 → ¬ (x i2 j2 < x i1 j1 ∧ x i2 j2 < x i3 j3)

instance {n : ℕ} (x : Fin n → Fin 4 → Fin 3) : Decidable (AntidiagonalsUnimodal x) := by
  unfold AntidiagonalsUnimodal; infer_instance

/-- A224258(n): the number of `n X 4` arrays with entries 0..2 whose rows, diagonals and antidiagonals are unimodal and whose columns are nondecreasing. -/
def a (n : ℕ) : ℕ :=
  (Finset.univ.filter (fun x : Fin n → Fin 4 → Fin 3 => RowsUnimodal x ∧ ColumnsNondecreasing x ∧ DiagonalsUnimodal x ∧ AntidiagonalsUnimodal x)).card

/-- Hardin's empirical formula and Barker's conjectured g.f. and recurrence. -/
theorem main :
    (∀ n : ℕ, 2 < n → (a n : ℚ) = 41/4032 * (n : ℚ) ^ 8 + 9/112 * (n : ℚ) ^ 7 + 349/480 * (n : ℚ) ^ 6 + 69/20 * (n : ℚ) ^ 5 + 1325/192 * (n : ℚ) ^ 4 + 1571/48 * (n : ℚ) ^ 3 + 87503/5040 * (n : ℚ) ^ 2 - 21949/420 * (n : ℚ) + 43) ∧
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) * (1 - X) ^ 9 =
      X * (46 + 134 * X - 180 * X ^ 2 + 467 * X ^ 3 + 29 * X ^ 4 - 416 * X ^ 5 + 534 * X ^ 6 - 255 * X ^ 7 + 61 * X ^ 8 - 12 * X ^ 9 + 2 * X ^ 10) ∧
    ∀ n : ℕ, 11 < n → (a n : ℤ) = 9 * a (n - 1) - 36 * a (n - 2) + 84 * a (n - 3) - 126 * a (n - 4) + 126 * a (n - 5) - 84 * a (n - 6) + 36 * a (n - 7) - 9 * a (n - 8) + a (n - 9) := by
  sorry

end OMA.S_oeis_a224258

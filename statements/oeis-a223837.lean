import Mathlib

/-!
# A223837: Number of n X 7 0..1 arrays with rows, diagonals and antidiagonals unimodal and columns nondecreasing.

Source: https://oeis.org/A223837
Credit: @prathameshnium (agent: Claude Code, model claude-opus-5-5)

The entry (R. H. Hardin, Mar 27 2013; column 7 of A223838; DATA 29, 239, 926, 2578, 6159, ...) records in its FORMULA section:

  Empirical: a(n) = (4/315)*n^7 - (1/45)*n^6 + (28/45)*n^5 + (113/72)*n^4 + (2137/180)*n^3 + (14023/360)*n^2 + (13159/140)*n - 339 for n>4.
  Conjectures from Colin Barker, Aug 23 2018:
  G.f.: x*(29 + 7*x - 174*x^2 + 238*x^3 + 109*x^4 - 256*x^5 + 45*x^6 + 111*x^7 - 27*x^8 - 26*x^9 + 6*x^10 + 2*x^11) / (1 - x)^8.
  a(n) = 8*a(n-1) - 28*a(n-2) + 56*a(n-3) - 70*a(n-4) + 56*a(n-5) - 28*a(n-6) + 8*a(n-7) - a(n-8) for n>12.

Conventions:
* Offset 1. An `n X 7` array with entries 0..1 is `x : Fin n → Fin 7 → Fin 2`, where `x i j` is
  the entry in row `i` and column `j`. `a n` counts such arrays for every `n`; the conjectures concern `n ≥ 1`.
* A finite sequence is unimodal when it is weakly increasing and then weakly decreasing. Equivalently, no
  entry is strictly smaller than both an earlier and a later entry of the sequence; the definitions below
  use this second form. Rows are read left to right and columns top to bottom.
* Columns are nondecreasing: entries do not decrease going down a column.
* A diagonal is the set of cells with `j - i` constant, an antidiagonal the set with `i + j` constant;
  both are read in order of increasing `i` (the direction does not matter for unimodality).
* Empirical formula: stated over ℚ for `n > 4`. G.f.: an identity of formal power series over ℚ,
  with coefficient 0 at `x^0` (offset 1). Recurrence: stated in ℤ for `n > 12`.

Numerical check: a Python copy of these definitions gives the DATA of the entry (29, 239, 926, 2578, ...) by
brute force over all arrays for small `n`.
-/

namespace OMA.S_oeis_a223837

open PowerSeries

/-- Every row is unimodal. -/
def RowsUnimodal {n : ℕ} (x : Fin n → Fin 7 → Fin 2) : Prop :=
  ∀ i : Fin n, ∀ j1 j2 j3 : Fin 7, j1 < j2 → j2 < j3 → ¬ (x i j2 < x i j1 ∧ x i j2 < x i j3)

instance {n : ℕ} (x : Fin n → Fin 7 → Fin 2) : Decidable (RowsUnimodal x) := by
  unfold RowsUnimodal; infer_instance

/-- Every column is nondecreasing downwards. -/
def ColumnsNondecreasing {n : ℕ} (x : Fin n → Fin 7 → Fin 2) : Prop :=
  ∀ i1 i2 : Fin n, ∀ j : Fin 7, i1 ≤ i2 → x i1 j ≤ x i2 j

instance {n : ℕ} (x : Fin n → Fin 7 → Fin 2) : Decidable (ColumnsNondecreasing x) := by
  unfold ColumnsNondecreasing; infer_instance

/-- Every diagonal (cells with `j - i` constant, read by increasing `i`) is unimodal. -/
def DiagonalsUnimodal {n : ℕ} (x : Fin n → Fin 7 → Fin 2) : Prop :=
  ∀ i1 i2 i3 : Fin n, ∀ j1 j2 j3 : Fin 7, i1 < i2 → i2 < i3 → (j1 : ℕ) + i2 = j2 + i1 →
    (j2 : ℕ) + i3 = j3 + i2 → ¬ (x i2 j2 < x i1 j1 ∧ x i2 j2 < x i3 j3)

instance {n : ℕ} (x : Fin n → Fin 7 → Fin 2) : Decidable (DiagonalsUnimodal x) := by
  unfold DiagonalsUnimodal; infer_instance

/-- Every antidiagonal (cells with `i + j` constant, read by increasing `i`) is unimodal. -/
def AntidiagonalsUnimodal {n : ℕ} (x : Fin n → Fin 7 → Fin 2) : Prop :=
  ∀ i1 i2 i3 : Fin n, ∀ j1 j2 j3 : Fin 7, i1 < i2 → i2 < i3 → (i1 : ℕ) + j1 = i2 + j2 →
    (i2 : ℕ) + j2 = i3 + j3 → ¬ (x i2 j2 < x i1 j1 ∧ x i2 j2 < x i3 j3)

instance {n : ℕ} (x : Fin n → Fin 7 → Fin 2) : Decidable (AntidiagonalsUnimodal x) := by
  unfold AntidiagonalsUnimodal; infer_instance

/-- A223837(n): the number of `n X 7` arrays with entries 0..1 whose rows, diagonals and antidiagonals are unimodal and whose columns are nondecreasing. -/
def a (n : ℕ) : ℕ :=
  (Finset.univ.filter (fun x : Fin n → Fin 7 → Fin 2 => RowsUnimodal x ∧ ColumnsNondecreasing x ∧ DiagonalsUnimodal x ∧ AntidiagonalsUnimodal x)).card

/-- Hardin's empirical formula and Barker's conjectured g.f. and recurrence. -/
theorem main :
    (∀ n : ℕ, 4 < n → (a n : ℚ) = 4/315 * (n : ℚ) ^ 7 - 1/45 * (n : ℚ) ^ 6 + 28/45 * (n : ℚ) ^ 5 + 113/72 * (n : ℚ) ^ 4 + 2137/180 * (n : ℚ) ^ 3 + 14023/360 * (n : ℚ) ^ 2 + 13159/140 * (n : ℚ) - 339) ∧
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) * (1 - X) ^ 8 =
      X * (29 + 7 * X - 174 * X ^ 2 + 238 * X ^ 3 + 109 * X ^ 4 - 256 * X ^ 5 + 45 * X ^ 6 + 111 * X ^ 7 - 27 * X ^ 8 - 26 * X ^ 9 + 6 * X ^ 10 + 2 * X ^ 11) ∧
    ∀ n : ℕ, 12 < n → (a n : ℤ) = 8 * a (n - 1) - 28 * a (n - 2) + 56 * a (n - 3) - 70 * a (n - 4) + 56 * a (n - 5) - 28 * a (n - 6) + 8 * a (n - 7) - a (n - 8) := by
  sorry

end OMA.S_oeis_a223837

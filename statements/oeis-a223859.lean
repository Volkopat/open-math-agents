import Mathlib

/-!
# A223859: Number of n X 3 0..3 arrays with rows and antidiagonals unimodal and columns nondecreasing.

Source: https://oeis.org/A223859
Credit: @prathameshnium (agent: Claude Code, model claude-opus-5-5)

The entry (R. H. Hardin, Mar 28 2013; column 3 of A223864; DATA 50, 684, 4884, 24199, 93731, ...) records in its FORMULA section:

  Empirical: a(n) = (353/181440)*n^9 + (353/10080)*n^8 + (9707/30240)*n^7 + (13/8)*n^6 + (45713/8640)*n^5 + (1809/160)*n^4 + (332021/22680)*n^3 + (6569/504)*n^2 + (7241/1260)*n - 2.
  Conjectures from Colin Barker, Aug 24 2018:
  G.f.: x*(50 + 184*x + 294*x^2 + 139*x^3 - 59*x^4 + 165*x^5 - 117*x^6 + 66*x^7 - 18*x^8 + 2*x^9) / (1 - x)^10.
  a(n) = 10*a(n-1) - 45*a(n-2) + 120*a(n-3) - 210*a(n-4) + 252*a(n-5) - 210*a(n-6) + 120*a(n-7) - 45*a(n-8) + 10*a(n-9) - a(n-10) for n>10.

Conventions:
* Offset 1. An `n X 3` array with entries 0..3 is `x : Fin n → Fin 3 → Fin 4`, where `x i j` is
  the entry in row `i` and column `j`. `a n` counts such arrays for every `n`; the conjectures concern `n ≥ 1`.
* A finite sequence is unimodal when it is weakly increasing and then weakly decreasing. Equivalently, no
  entry is strictly smaller than both an earlier and a later entry of the sequence; the definitions below
  use this second form. Rows are read left to right and columns top to bottom.
* Columns are nondecreasing: entries do not decrease going down a column.
* A diagonal is the set of cells with `j - i` constant, an antidiagonal the set with `i + j` constant;
  both are read in order of increasing `i` (the direction does not matter for unimodality).
* Empirical formula: stated over ℚ for `n > 0` (all `n ≥ 1`). G.f.: an identity of formal power series over ℚ,
  with coefficient 0 at `x^0` (offset 1). Recurrence: stated in ℤ for `n > 10`.

Numerical check: a Python copy of these definitions gives the DATA of the entry (50, 684, 4884, 24199, ...) by
brute force over all arrays for small `n`.
-/

namespace OMA.S_oeis_a223859

open PowerSeries

/-- Every row is unimodal. -/
def RowsUnimodal {n : ℕ} (x : Fin n → Fin 3 → Fin 4) : Prop :=
  ∀ i : Fin n, ∀ j1 j2 j3 : Fin 3, j1 < j2 → j2 < j3 → ¬ (x i j2 < x i j1 ∧ x i j2 < x i j3)

instance {n : ℕ} (x : Fin n → Fin 3 → Fin 4) : Decidable (RowsUnimodal x) := by
  unfold RowsUnimodal; infer_instance

/-- Every column is nondecreasing downwards. -/
def ColumnsNondecreasing {n : ℕ} (x : Fin n → Fin 3 → Fin 4) : Prop :=
  ∀ i1 i2 : Fin n, ∀ j : Fin 3, i1 ≤ i2 → x i1 j ≤ x i2 j

instance {n : ℕ} (x : Fin n → Fin 3 → Fin 4) : Decidable (ColumnsNondecreasing x) := by
  unfold ColumnsNondecreasing; infer_instance

/-- Every antidiagonal (cells with `i + j` constant, read by increasing `i`) is unimodal. -/
def AntidiagonalsUnimodal {n : ℕ} (x : Fin n → Fin 3 → Fin 4) : Prop :=
  ∀ i1 i2 i3 : Fin n, ∀ j1 j2 j3 : Fin 3, i1 < i2 → i2 < i3 → (i1 : ℕ) + j1 = i2 + j2 →
    (i2 : ℕ) + j2 = i3 + j3 → ¬ (x i2 j2 < x i1 j1 ∧ x i2 j2 < x i3 j3)

instance {n : ℕ} (x : Fin n → Fin 3 → Fin 4) : Decidable (AntidiagonalsUnimodal x) := by
  unfold AntidiagonalsUnimodal; infer_instance

/-- A223859(n): the number of `n X 3` arrays with entries 0..3 whose rows and antidiagonals are unimodal and whose columns are nondecreasing. -/
def a (n : ℕ) : ℕ :=
  (Finset.univ.filter (fun x : Fin n → Fin 3 → Fin 4 => RowsUnimodal x ∧ ColumnsNondecreasing x ∧ AntidiagonalsUnimodal x)).card

/-- Hardin's empirical formula and Barker's conjectured g.f. and recurrence. -/
theorem main :
    (∀ n : ℕ, 0 < n → (a n : ℚ) = 353/181440 * (n : ℚ) ^ 9 + 353/10080 * (n : ℚ) ^ 8 + 9707/30240 * (n : ℚ) ^ 7 + 13/8 * (n : ℚ) ^ 6 + 45713/8640 * (n : ℚ) ^ 5 + 1809/160 * (n : ℚ) ^ 4 + 332021/22680 * (n : ℚ) ^ 3 + 6569/504 * (n : ℚ) ^ 2 + 7241/1260 * (n : ℚ) - 2) ∧
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) * (1 - X) ^ 10 =
      X * (50 + 184 * X + 294 * X ^ 2 + 139 * X ^ 3 - 59 * X ^ 4 + 165 * X ^ 5 - 117 * X ^ 6 + 66 * X ^ 7 - 18 * X ^ 8 + 2 * X ^ 9) ∧
    ∀ n : ℕ, 10 < n → (a n : ℤ) = 10 * a (n - 1) - 45 * a (n - 2) + 120 * a (n - 3) - 210 * a (n - 4) + 252 * a (n - 5) - 210 * a (n - 6) + 120 * a (n - 7) - 45 * a (n - 8) + 10 * a (n - 9) - a (n - 10) := by
  sorry

end OMA.S_oeis_a223859

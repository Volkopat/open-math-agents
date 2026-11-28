import Mathlib

/-!
# A224145: Number of n X 7 0..1 arrays with rows and antidiagonals unimodal and columns nondecreasing.

Source: https://oeis.org/A224145
Credit: @prathameshnium (agent: Claude Code, model claude-opus-5-5)

The entry (R. H. Hardin, Mar 31 2013; column 7 of A224146; DATA 29, 239, 1037, 3296, 8838, ...) records in its FORMULA section:

  Empirical: a(n) = (4/315)*n^7 + (4/45)*n^6 + (34/45)*n^5 + (29/9)*n^4 + (508/45)*n^3 + (1156/45)*n^2 + (1328/35)*n - 161 for n>4.
  Conjectures from Colin Barker, Aug 28 2018:
  G.f.: x*(29 + 7*x - 63*x^2 + 68*x^3 + 152*x^4 - 199*x^5 + 28*x^6 + 71*x^7 - 21*x^8 - 12*x^9 + 3*x^10 + x^11) / (1 - x)^8.
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

Numerical check: a Python copy of these definitions gives the DATA of the entry (29, 239, 1037, 3296, ...) by
brute force over all arrays for small `n`.
-/

namespace OMA.S_oeis_a224145

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

/-- Every antidiagonal (cells with `i + j` constant, read by increasing `i`) is unimodal. -/
def AntidiagonalsUnimodal {n : ℕ} (x : Fin n → Fin 7 → Fin 2) : Prop :=
  ∀ i1 i2 i3 : Fin n, ∀ j1 j2 j3 : Fin 7, i1 < i2 → i2 < i3 → (i1 : ℕ) + j1 = i2 + j2 →
    (i2 : ℕ) + j2 = i3 + j3 → ¬ (x i2 j2 < x i1 j1 ∧ x i2 j2 < x i3 j3)

instance {n : ℕ} (x : Fin n → Fin 7 → Fin 2) : Decidable (AntidiagonalsUnimodal x) := by
  unfold AntidiagonalsUnimodal; infer_instance

/-- A224145(n): the number of `n X 7` arrays with entries 0..1 whose rows and antidiagonals are unimodal and whose columns are nondecreasing. -/
def a (n : ℕ) : ℕ :=
  (Finset.univ.filter (fun x : Fin n → Fin 7 → Fin 2 => RowsUnimodal x ∧ ColumnsNondecreasing x ∧ AntidiagonalsUnimodal x)).card

/-- Hardin's empirical formula and Barker's conjectured g.f. and recurrence. -/
theorem main :
    (∀ n : ℕ, 4 < n → (a n : ℚ) = 4/315 * (n : ℚ) ^ 7 + 4/45 * (n : ℚ) ^ 6 + 34/45 * (n : ℚ) ^ 5 + 29/9 * (n : ℚ) ^ 4 + 508/45 * (n : ℚ) ^ 3 + 1156/45 * (n : ℚ) ^ 2 + 1328/35 * (n : ℚ) - 161) ∧
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) * (1 - X) ^ 8 =
      X * (29 + 7 * X - 63 * X ^ 2 + 68 * X ^ 3 + 152 * X ^ 4 - 199 * X ^ 5 + 28 * X ^ 6 + 71 * X ^ 7 - 21 * X ^ 8 - 12 * X ^ 9 + 3 * X ^ 10 + X ^ 11) ∧
    ∀ n : ℕ, 12 < n → (a n : ℤ) = 8 * a (n - 1) - 28 * a (n - 2) + 56 * a (n - 3) - 70 * a (n - 4) + 56 * a (n - 5) - 28 * a (n - 6) + 8 * a (n - 7) - a (n - 8) := by
  sorry

end OMA.S_oeis_a224145
